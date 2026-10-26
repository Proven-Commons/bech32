// The Rust oracle for tests/run_tests.py: the bech32 crate of
// rust-bitcoin, at the version Cargo.lock pins, through its
// `primitives` module, which reads and writes the 5-bit values
// themselves (the crate-level `encode` and `decode` take and give
// 8-bit bytes).
//
// Each line of standard input is one request, with fields in hex as
// for `bech32 serve` (`-` for an empty field):
//
//   d STRING               UncheckedHrpstring::new, then the Bech32
//                          checksum, else the Bech32m one
//   e VARIANT HRP VALUES   Hrp::parse, then Fe32IterExt::with_checksum
//
// Each answer is `OK VARIANT HRP VALUES` for a decoding, `OK STRING`
// for an encoding, `FAIL` and the library's error with its spaces
// replaced, or `error` for a line this program cannot read.

use std::io::{self, BufRead, BufWriter, Write};

use bech32::primitives::decode::UncheckedHrpstring;
use bech32::primitives::iter::Fe32IterExt;
use bech32::{Bech32, Bech32m, Fe32, Hrp};

fn field(f: &str) -> Option<Vec<u8>> {
    if f == "-" {
        return Some(Vec::new());
    }
    if f.is_empty() || f.len() % 2 != 0 {
        return None;
    }
    (0..f.len())
        .step_by(2)
        .map(|i| f.get(i..i + 2).and_then(|h| u8::from_str_radix(h, 16).ok()))
        .collect()
}

fn to_field(bs: &[u8]) -> String {
    if bs.is_empty() {
        return "-".to_string();
    }
    bs.iter().map(|b| format!("{:02x}", b)).collect()
}

// The library's error on one line: escaped, with no spaces.
fn fail<E: std::fmt::Display>(e: E) -> String {
    format!(
        "FAIL {}",
        e.to_string().escape_default().to_string().replace(' ', "_")
    )
}

fn decode(s: &str) -> String {
    let unchecked = match UncheckedHrpstring::new(s) {
        Ok(u) => u,
        Err(e) => return fail(e),
    };
    let (name, checked) = if unchecked.has_valid_checksum::<Bech32>() {
        ("bech32", unchecked.remove_checksum::<Bech32>())
    } else if unchecked.has_valid_checksum::<Bech32m>() {
        ("bech32m", unchecked.remove_checksum::<Bech32m>())
    } else {
        return match unchecked.validate_checksum::<Bech32>() {
            Err(e) => fail(e),
            Ok(()) => "FAIL checksum".to_string(),
        };
    };
    let hrp = checked.hrp().to_lowercase();
    let values: Vec<u8> = checked
        .fe32_iter::<std::iter::Empty<u8>>()
        .map(|fe| fe.to_u8())
        .collect();
    format!(
        "OK {} {} {}",
        name,
        to_field(hrp.as_bytes()),
        to_field(&values)
    )
}

fn encode(variant: &str, hrp: &str, values: &[u8]) -> String {
    let hrp = match Hrp::parse(hrp) {
        Ok(h) => h,
        Err(e) => return fail(e),
    };
    let mut fes = Vec::with_capacity(values.len());
    for &v in values {
        match Fe32::try_from(v) {
            Ok(fe) => fes.push(fe),
            Err(e) => return fail(e),
        }
    }
    let s: String = match variant {
        "bech32" => fes
            .into_iter()
            .with_checksum::<Bech32>(&hrp)
            .chars()
            .collect(),
        "bech32m" => fes
            .into_iter()
            .with_checksum::<Bech32m>(&hrp)
            .chars()
            .collect(),
        _ => return "error".to_string(),
    };
    format!("OK {}", to_field(s.as_bytes()))
}

fn answer(line: &str) -> String {
    let parts: Vec<&str> = line.split(' ').collect();
    match parts.as_slice() {
        ["d", s] => match field(s).map(String::from_utf8) {
            Some(Ok(s)) => decode(&s),
            _ => "error".to_string(),
        },
        ["e", variant, hrp, values] => match (field(hrp).map(String::from_utf8), field(values)) {
            (Some(Ok(hrp)), Some(values)) => encode(variant, &hrp, &values),
            _ => "error".to_string(),
        },
        _ => "error".to_string(),
    }
}

fn main() {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = BufWriter::with_capacity(1 << 20, stdout.lock());
    for line in stdin.lock().split(b'\n') {
        let line = line.expect("read standard input");
        let text = String::from_utf8_lossy(&line);
        let text = text.strip_suffix('\r').unwrap_or(&text);
        writeln!(out, "{}", answer(text)).expect("write standard output");
    }
}
