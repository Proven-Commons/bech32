#!/usr/bin/env python3
"""Differential tests: the Lean Bech32 and Bech32m encoder and decoder
against a model of BIP 173 and BIP 350 and five implementations.

The tool answers `decode` and `encode` requests (see the header of
Main.lean). Its answers are checked two ways.

1. Against `model_decode` and `model_encode`, Python transcriptions of
   the rules of BIP 173 ("Bech32", "Encoders MUST always output an all
   lowercase Bech32 string", "Decoders MUST NOT accept ... mixed case
   strings") with its normative checksum code, `bech32_polymod` and
   `bech32_hrp_expand`, and the constant 0x2bc830a3 of BIP 350. They
   share nothing with the Lean code. Every answer must agree.

2. Against five oracles, on every input:

   - sipa Python: `bech32_decode` and `bech32_encode` of
     ref/python/segwit_addr.py of https://github.com/sipa/bech32 at
     SIPA_COMMIT, unchanged in tests/oracles/sipa;
   - sipa C: `bech32_decode` and `bech32_encode` of ref/c/segwit_addr.c
     at the same commit, unchanged in tests/oracles/sipa, compiled here
     with `cc` and driven by tests/oracles/sipa/wrapper.c;
   - npm: the `bech32` package of bitcoinjs, version 2.0.0, installed
     with `npm ci` into .lake/oracle-node from
     tests/oracles/node/package-lock.json, which pins its integrity hash,
     and driven by tests/oracles/node/oracle.js;
   - Go: `DecodeGeneric`, `Encode` and `EncodeM` of the bech32 package
     of github.com/btcsuite/btcd/btcutil, at the release
     tests/oracles/go/go.mod pins (go.sum holds its hash), through the
     program there;
   - Rust: the `bech32` crate of rust-bitcoin, version 0.11.1, pinned in
     tests/oracles/rust/Cargo.lock, through its `primitives` module,
     which reads and writes the 5-bit values themselves.

   An oracle that cannot be built or started is left out, and the
   record says so on its `- Oracles left out:` line. A disagreement is
   allowed only where the tool refuses and the oracle answers, for a
   known reason that the model confirms: the model, on the input the
   oracle actually reads or with only the checks the oracle makes,
   gives the oracle's answer. Each is counted under its reason:

   - Rust decodes strings longer than 90 characters: its limit is the
     code length, 1023. The model without the limit agrees.
   - npm lower-cases with Unicode rules before it reads a string, so
     the Kelvin sign U+212A reads as `k` in an upper case string. The
     model on the string with `K` in its place agrees.
   - sipa C takes C strings, which end at the first NUL. The model on
     the string, or the HRP, up to the NUL agrees.
   - The encoders check less than BIP 173 asks. sipa Python checks
     nothing, and writes an upper case HRP as it is. sipa C and npm
     write an empty HRP. npm lower-cases the HRP with Unicode rules
     first. Go checks nothing, lower-cases the HRP with Unicode rules
     and takes the checksum over its UTF-8 bytes. Rust lower-cases the
     HRP and has no length limit. The model's encoder, with only the
     checks and the lower-casing the oracle makes, agrees.

   Any other disagreement is a failure.

The record also counts two of the proved claims: no single
substitution in the data part of a valid string gives a string that
decodes (`Bech32.Spec.one_substitution`), and inserting `q` before a final `p`
keeps every Bech32 string that still fits in 90 characters valid and no
Bech32m string valid (`Bech32.Spec.insert_q_bech32`, `Bech32.Spec.insert_q_bech32m`).

Inputs come from a recorded seed, after fixed sets:

- every string of BIP 173 and BIP 350, valid and invalid, the segwit
  address lists read as strings, and the encodings of the valid ones;
- edge cases: lengths 89, 90 and 91 (and 120, 1023 and 1024), HRPs of
  82, 83 and 84 characters, an empty HRP, the separator alone, data
  parts of 5 and 6 characters, every printable ASCII character in the
  HRP, characters 0, 32, 127, 128 and 255 and others outside ASCII
  anywhere in a string, mixed case, the HRP's case alone differing, `1`
  inside the HRP, the Kelvin sign, NUL; and encodings at the same
  limits;
- every string of up to four characters over `q`, `A`, `1`, `?` and
  `u+00FC`;
- random valid strings from random HRPs, data and variants, in either
  case, and their encodings; for each, every substitution at one
  sampled position (in the data part, each of the 31 other data
  characters), an insertion, a deletion, an adjacent swap and a case
  flip;
- random valid strings ending in `p`, with `q` inserted before the `p`;
- random strings over a small alphabet, and random encodings with HRPs
  of every kind, valid or not;
- malformed requests, which the tool must answer with `error`.

Every seventh request ends in CR LF.

    python3 tests/run_tests.py [--seed N] [--count N] [--no-oracles]

`--count` is the number of random valid strings. `--no-oracles` leaves
every oracle out and compares the tool with the model alone, as
tests/plant_bugs.py does. The script builds the executable and the
oracles first, writes tests/TEST-RESULTS.md, and exits non-zero if any
check fails.
"""

import argparse
import hashlib
import importlib.util
import itertools
import json
import os
import platform
import random
import re
import shutil
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "bech32"
ORACLES = ROOT / "tests" / "oracles"
SIPA_SRC = ORACLES / "sipa"
SIPA_COMMIT = "7a7d7ab158db7078a333384e0e918c90dbc42917"
SIPA_SHA256 = {
    "segwit_addr.py": "2884ce04a36c8374c4249177cd90e91e545ac73b5c9260307bbeb74ae2e9de0f",
    "segwit_addr.c": "aa73529c41142d2a9fed384676910943692236eda2ec583f96a95b5283c3042d",
    "segwit_addr.h": "1b70ce1aad01cd8e99ed1814e191d80a1c47feda65afb652eebef3be35620733",
}
C_EXE = ROOT / ".lake" / "oracle-sipa" / "sipa-c-oracle"
NODE_SRC = ORACLES / "node"
NODE_DIR = ROOT / ".lake" / "oracle-node"
GO_SRC = ORACLES / "go"
GO_EXE = ROOT / ".lake" / "oracle-go" / "go-oracle"
RUST_SRC = ORACLES / "rust"
RUST_TARGET = ROOT / ".lake" / "oracle-rust"
RUST_EXE = RUST_TARGET / "release" / "bech32-oracle"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
TIMEOUT = 3600
BUILD_TIMEOUT = 3600

# ---------------------------------------------------------------------
# The model: BIP 173 and BIP 350.

CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
VARIANTS = ("bech32", "bech32m")
# The constant the checksum gives: 1 (BIP 173), BECH32M_CONST (BIP 350).
CONST = {"bech32": 1, "bech32m": 0x2bc830a3}


def bech32_polymod(values):
    """BIP 173, as printed there."""
    GEN = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
    chk = 1
    for v in values:
        b = (chk >> 25)
        chk = (chk & 0x1ffffff) << 5 ^ v
        for i in range(5):
            chk ^= GEN[i] if ((b >> i) & 1) else 0
    return chk


def bech32_hrp_expand(codes):
    """BIP 173's `bech32_hrp_expand`, on the HRP's character codes."""
    return [x >> 5 for x in codes] + [0] + [x & 31 for x in codes]


def is_upper(c):
    return "A" <= c <= "Z"


def is_lower(c):
    return "a" <= c <= "z"


def ascii_lower(s):
    return "".join(chr(ord(c) + 32) if is_upper(c) else c for c in s)


def model_decode(s, limit=90):
    """Read `s` by BIP 173 and BIP 350. Returns ((variant, HRP in lower
    case, data values without the checksum) or None, why it fails or
    None). With `limit=None` the 90-character limit is dropped, as some
    oracles drop it; the HRP stays within 83 characters."""
    # "A Bech32 string is at most 90 characters long."
    if limit is not None and len(s) > limit:
        return None, "longer than 90 characters"
    # "Decoders MUST NOT accept strings where some characters are
    # uppercase and some are lowercase."
    if any(is_upper(c) for c in s) and any(is_lower(c) for c in s):
        return None, "mixed case"
    # "The lowercase form is used when determining a character's value
    # for checksum purposes."
    low = ascii_lower(s)
    # "In case '1' is allowed inside the human-readable part, the last
    # one in the string is the separator."
    pos = low.rfind("1")
    if pos < 0:
        return None, "no separator"
    hrp, part = low[:pos], low[pos + 1:]
    # "This part MUST contain 1 to 83 US-ASCII characters, with each
    # character having a value in the range [33-126]."
    if not 1 <= len(hrp) <= 83:
        return None, "an HRP of no characters or more than 83"
    if any(not 33 <= ord(c) <= 126 for c in hrp):
        return None, "an HRP character outside 33 to 126"
    # "The data part, which is at least 6 characters long and only
    # consists of alphanumeric characters excluding '1', 'b', 'i', and
    # 'o'", each standing for its place in the table.
    if len(part) < 6:
        return None, "a data part of fewer than 6 characters"
    if any(c not in CHARSET for c in part):
        return None, "a character that is not a data character"
    values = [CHARSET.index(c) for c in part]
    pm = bech32_polymod(bech32_hrp_expand([ord(c) for c in hrp]) + values)
    for v in VARIANTS:
        if pm == CONST[v]:
            return (v, hrp, tuple(values[:-6])), None
    return None, "the checksum"


def create_checksum(variant, codes, data):
    """BIP 173's `bech32_create_checksum`, with the constant of the
    variant (BIP 350), over the HRP's character codes `codes`."""
    values = bech32_hrp_expand(codes) + list(data)
    polymod = bech32_polymod(values + [0, 0, 0, 0, 0, 0]) ^ CONST[variant]
    return [(polymod >> 5 * (5 - i)) & 31 for i in range(6)]


def raw_encode(variant, hrp, data, codes=None):
    """BIP 173's `bech32_encode`, with no check: the HRP, `1`, then the
    characters of the data and of the checksum."""
    codes = [ord(c) for c in hrp] if codes is None else codes
    combined = list(data) + create_checksum(variant, codes, data)
    return hrp + "1" + "".join(CHARSET[d] for d in combined)


def model_encode(variant, hrp, data):
    """Write the string, or (None, why): the HRP must be 1 or more
    characters in 33 to 126 with no upper case letter ("Encoders MUST
    always output an all lowercase Bech32 string"), and the string at
    most 90 characters."""
    if hrp == "":
        return None, "an empty HRP"
    if any(not 33 <= ord(c) <= 126 for c in hrp):
        return None, "an HRP character outside 33 to 126"
    if any(is_upper(c) for c in hrp):
        return None, "an upper case letter in the HRP"
    if len(hrp) + 1 + len(data) + 6 > 90:
        return None, "longer than 90 characters"
    return raw_encode(variant, hrp, data), None


# ---------------------------------------------------------------------
# Running a program over request lines.

def run_lines(cmd, lines, timeout=TIMEOUT, cwd=None, env=None):
    """Send `lines` to `cmd` and return its answer lines and a note on
    how the run failed, or None."""
    raw = "".join(lines).encode("utf-8")
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, cwd=cwd, env=env)
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf):
        while chunk := stream.read1(1 << 16):
            buf += chunk

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out)),
               threading.Thread(target=drain, args=(proc.stderr, err))]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    return answers, problem


def hexf(s):
    """A string as a request field: the hex of its UTF-8 bytes, `-` when
    empty."""
    return s.encode("utf-8").hex() or "-"


def valf(data):
    return bytes(data).hex() or "-"


def unhex(f):
    return b"" if f == "-" else bytes.fromhex(f)


def parse_answer(kind, a):
    """An answer in the form of `bech32 serve`: (variant, HRP, data) or
    a string, None for FAIL, or ("unreadable", the answer)."""
    try:
        if a == "FAIL" or a.startswith("FAIL "):
            return None
        parts = a.split(" ")
        if kind == "d" and len(parts) == 4 and parts[0] == "OK" and parts[1] in VARIANTS:
            return (parts[1], unhex(parts[2]).decode("utf-8"), tuple(unhex(parts[3])))
        if kind == "e" and len(parts) == 2 and parts[0] == "OK":
            return unhex(parts[1]).decode("utf-8")
    except (ValueError, UnicodeDecodeError):
        pass
    return ("unreadable", a)


def request_line(kind, x):
    if kind == "d":
        return f"d {hexf(x)}\n"
    v, hrp, data = x
    return f"e {v} {hexf(hrp)} {valf(data)}\n"


# ---------------------------------------------------------------------
# The oracles. Each setup returns an object with `name`, `version` and
# `answers(items)`, or raises OracleUnavailable.

class OracleUnavailable(Exception):
    pass


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_sipa_files():
    for name, want in SIPA_SHA256.items():
        got = sha256(SIPA_SRC / name)
        if got != want:
            raise OracleUnavailable(f"{name} has SHA-256 {got}, not the {want} of SOURCE.md")


class ProcessOracle:
    def __init__(self, name, version, cmd, env=None):
        self.name, self.version, self.cmd, self.env = name, version, cmd, env

    def answers(self, items):
        answers, problem = run_lines(self.cmd, [request_line(k, x) for _, k, x in items],
                                     env=self.env)
        if problem or len(answers) != len(items):
            raise RuntimeError(f"{self.name} oracle: "
                               f"{problem or f'{len(answers)} answers for {len(items)} requests'}")
        return [parse_answer(k, a) for (_, k, _), a in zip(items, answers)]


class SipaPython:
    name = "sipa Python"

    def __init__(self):
        check_sipa_files()
        spec = importlib.util.spec_from_file_location("sipa_segwit_addr",
                                                      SIPA_SRC / "segwit_addr.py")
        self.mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.mod)
        self.version = (f"`bech32_decode` and `bech32_encode` of `ref/python/segwit_addr.py`, "
                        f"sipa/bech32 commit {SIPA_COMMIT}, SHA-256 "
                        f"{SIPA_SHA256['segwit_addr.py']}, on Python {platform.python_version()}")
        enc = self.mod.Encoding
        self.spec = {"bech32": enc.BECH32, "bech32m": enc.BECH32M}
        self.names = {enc.BECH32: "bech32", enc.BECH32M: "bech32m"}

    def one(self, kind, x):
        try:
            if kind == "d":
                hrp, data, spec = self.mod.bech32_decode(x)
                return None if hrp is None else (self.names[spec], hrp, tuple(data))
            v, hrp, data = x
            return self.mod.bech32_encode(hrp, list(data), self.spec[v])
        except Exception as e:  # an exception is an answer to report, not a crash
            return ("unreadable", f"{type(e).__name__}: {e}")

    def answers(self, items):
        return [self.one(k, x) for _, k, x in items]


def first_line(cmd):
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        return (out.stdout or out.stderr).strip().splitlines()[0]
    except (OSError, subprocess.SubprocessError, IndexError):
        return "unknown"


def setup_sipa_c():
    check_sipa_files()
    C_EXE.parent.mkdir(parents=True, exist_ok=True)
    try:
        subprocess.run(["cc", "-O2", "-o", str(C_EXE), str(SIPA_SRC / "segwit_addr.c"),
                        str(SIPA_SRC / "wrapper.c")], check=True, timeout=BUILD_TIMEOUT,
                       capture_output=True)
    except (OSError, subprocess.SubprocessError) as e:
        raise OracleUnavailable(f"`cc` did not build it: {e}")
    return ProcessOracle("sipa C", f"`bech32_decode` and `bech32_encode` of "
                         f"`ref/c/segwit_addr.c`, sipa/bech32 commit {SIPA_COMMIT}, SHA-256 "
                         f"{SIPA_SHA256['segwit_addr.c']}, compiled with "
                         f"{first_line(['cc', '--version'])}", [str(C_EXE)])


def setup_npm():
    node = first_line(["node", "--version"])
    if node == "unknown":
        raise OracleUnavailable("`node --version` did not run")
    lock = json.loads((NODE_SRC / "package-lock.json").read_text(encoding="utf-8"))
    pinned = lock["packages"]["node_modules/bech32"]
    installed = NODE_DIR / "node_modules" / "bech32" / "package.json"
    same_lock = ((NODE_DIR / "package-lock.json").exists()
                 and (NODE_DIR / "package-lock.json").read_bytes()
                 == (NODE_SRC / "package-lock.json").read_bytes())
    if not (same_lock and installed.exists()):
        NODE_DIR.mkdir(parents=True, exist_ok=True)
        for name in ("package.json", "package-lock.json"):
            shutil.copyfile(NODE_SRC / name, NODE_DIR / name)
        try:
            # npm ci installs exactly what the lock file names, and
            # checks each package against its integrity hash.
            subprocess.run(["npm", "ci", "--ignore-scripts", "--no-audit", "--no-fund"],
                           cwd=NODE_DIR, check=True, capture_output=True, timeout=BUILD_TIMEOUT)
        except (OSError, subprocess.SubprocessError) as e:
            raise OracleUnavailable(f"`npm ci` did not install it: {e}")
    version = json.loads(installed.read_text(encoding="utf-8"))["version"]
    if version != pinned["version"]:
        raise OracleUnavailable(f"bech32 {version} is installed, not {pinned['version']}")
    return ProcessOracle("npm", f"bech32 {version} (bitcoinjs), integrity "
                         f"{pinned['integrity']}, on Node {node}",
                         ["node", str(NODE_SRC / "oracle.js"), str(NODE_DIR / "node_modules")])


def setup_go():
    GO_EXE.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, GOFLAGS="-mod=readonly", CGO_ENABLED="0", GOTOOLCHAIN="local")
    try:
        subprocess.run(["go", "build", "-o", str(GO_EXE), "."], cwd=GO_SRC, check=True, env=env,
                       capture_output=True, timeout=BUILD_TIMEOUT)
    except (OSError, subprocess.SubprocessError) as e:
        raise OracleUnavailable(f"`go build` did not build it: {e}")
    mod = re.search(r"^require github.com/btcsuite/btcd/btcutil (\S+)",
                    (GO_SRC / "go.mod").read_text(encoding="utf-8"), re.M)
    sums = re.search(r"^github.com/btcsuite/btcd/btcutil \S+ (h1:\S+)",
                     (GO_SRC / "go.sum").read_text(encoding="utf-8"), re.M)
    return ProcessOracle("Go", f"package bech32 of github.com/btcsuite/btcd/btcutil "
                         f"{mod.group(1) if mod else '?'} ({sums.group(1) if sums else '?'}), "
                         f"built with {first_line(['go', 'version'])}", [str(GO_EXE)])


def setup_rust():
    env = dict(os.environ, CARGO_TARGET_DIR=str(RUST_TARGET))
    try:
        subprocess.run(["cargo", "build", "--release", "--locked", "--quiet", "--manifest-path",
                        str(RUST_SRC / "Cargo.toml")], check=True, env=env, capture_output=True,
                       timeout=BUILD_TIMEOUT)
    except (OSError, subprocess.SubprocessError) as e:
        raise OracleUnavailable(f"`cargo build` did not build it: {e}")
    lock = (RUST_SRC / "Cargo.lock").read_text(encoding="utf-8")
    m = re.search(r'name = "bech32"\nversion = "([^"]+)"\nsource = "[^"]+"\nchecksum = "([^"]+)"',
                  lock)
    return ProcessOracle("Rust", f"bech32 {m.group(1) if m else '?'} (rust-bitcoin), checksum "
                         f"{m.group(2) if m else '?'}, built with "
                         f"{first_line(['rustc', '--version'])}", [str(RUST_EXE)])


ORACLE_SETUPS = [("sipa Python", SipaPython), ("sipa C", setup_sipa_c), ("npm", setup_npm),
                 ("Go", setup_go), ("Rust", setup_rust)]

# ---------------------------------------------------------------------
# Why an oracle may differ. For each oracle, what the model gives on
# the input the oracle reads, with the checks the oracle makes; and the
# properties of an input that the reasons name.

KELVIN = "\u212a"


def utf16_length(s):
    return sum(2 if ord(c) > 0xFFFF else 1 for c in s)


def go_lower(s):
    """Go's strings.ToLower: the simple lower case mapping of each
    character. Python's str.lower gives the full mapping, which differs
    from it, among the characters these tests use, only for U+0130."""
    return "".join("i" if c == "\u0130" else (c.lower() if len(c.lower()) == 1 else c)
                   for c in s)


def oracle_model_decode(oracle, s):
    if oracle == "Rust":
        return model_decode(s, limit=None)[0] if len(s.encode("utf-8")) <= 1023 else None
    if oracle == "npm":
        return model_decode(s.replace(KELVIN, "K"))[0]
    if oracle == "sipa C":
        return model_decode(s.split("\0")[0])[0]
    return model_decode(s)[0]


def oracle_model_encode(oracle, variant, hrp, data):
    def in_range(h):
        return all(33 <= ord(c) <= 126 for c in h)

    if oracle == "sipa Python":
        return raw_encode(variant, hrp, data)
    if oracle == "sipa C":
        h = hrp.split("\0")[0]
        ok = in_range(h) and not any(is_upper(c) for c in h) and len(h) + 7 + len(data) <= 90
        return raw_encode(variant, h, data) if ok else None
    if oracle == "npm":
        h = hrp.lower()
        ok = utf16_length(hrp) + 7 + len(data) <= 90 and in_range(h)
        return raw_encode(variant, h, data) if ok else None
    if oracle == "Go":
        h = go_lower(hrp)
        return raw_encode(variant, h, data, codes=list(h.encode("utf-8")))
    if oracle == "Rust":
        mixed = any(is_upper(c) for c in hrp) and any(is_lower(c) for c in hrp)
        ok = 1 <= len(hrp.encode("utf-8")) <= 83 and in_range(hrp) and not mixed
        return raw_encode(variant, ascii_lower(hrp), data) if ok else None
    return model_encode(variant, hrp, data)[0]


DECODE_REASONS = {
    "Rust": {"long": "Rust has no 90-character limit (its limit is the code length, 1023)"},
    "npm": {"kelvin": "npm lower-cases with Unicode rules, so the Kelvin sign U+212A reads as k"},
    "sipa C": {"nul": "sipa C reads a C string, which ends at the first NUL"},
}

ENCODE_REASONS = {
    "sipa Python": {"empty": "writes an empty HRP",
                    "range": "writes HRP characters outside 33 to 126",
                    "upper": "writes an upper case HRP as it is, with its checksum",
                    "long": "has no 90-character limit"},
    "sipa C": {"empty": "writes an empty HRP",
               "nul": "reads the HRP as a C string, which ends at the first NUL"},
    "npm": {"empty": "writes an empty HRP",
            "upper": "lower-cases the HRP",
            "kelvin": "lower-cases the HRP with Unicode rules, which turn the Kelvin sign into k"},
    "Go": {"empty": "writes an empty HRP",
           "range": "writes HRP characters outside 33 to 126, lower-cased with Unicode rules, "
                    "with the checksum over their UTF-8 bytes",
           "upper": "lower-cases the HRP",
           "long": "has no 90-character limit"},
    "Rust": {"upper": "lower-cases the HRP",
             "long": "has no 90-character limit"},
}


def decode_props(s):
    props = set()
    if len(s) > 90:
        props.add("long")
    if KELVIN in s:
        props.add("kelvin")
    if "\0" in s:
        props.add("nul")
    return props


def encode_props(hrp, data):
    props = set()
    if hrp == "":
        props.add("empty")
    if any(not 33 <= ord(c) <= 126 for c in hrp):
        props.add("range")
    if any(is_upper(c) for c in hrp):
        props.add("upper")
    if len(hrp) + 7 + len(data) > 90:
        props.add("long")
    if KELVIN in hrp:
        props.add("kelvin")
    if "\0" in hrp:
        props.add("nul")
    return props


def difference_reason(oracle, kind, x, got, theirs):
    """The known reason the oracle's answer differs from the tool's,
    confirmed by the model, or None. Every reason is an oracle that
    accepts or writes what BIP 173 refuses, so it can excuse only a
    disagreement where the tool refused and the oracle answered."""
    if got is not None or theirs is None:
        return None
    if kind == "d":
        names = DECODE_REASONS.get(oracle, {})
        props = [names[p] for p in sorted(decode_props(x)) if p in names]
        if props and oracle_model_decode(oracle, x) == theirs:
            return "; ".join(props)
        return None
    names = ENCODE_REASONS.get(oracle, {})
    props = [names[p] for p in sorted(encode_props(x[1], x[2])) if p in names]
    if props and oracle_model_encode(oracle, *x) == theirs:
        return f"{oracle} " + "; ".join(props)
    return None


# ---------------------------------------------------------------------
# The fixed sets.

# BIP 173 and BIP 350, "Test vectors": each string with the variant it
# is valid in as a string, or None. For the segwit address lists the
# verdict is on the string, not the address: most invalid addresses are
# valid strings, and their variant follows from the BIP's reason. An
# address rejected for the wrong variant ("Bech32 instead of Bech32m")
# is valid in the variant named. One rejected for anything but its
# checksum, case or characters has a valid checksum: Bech32 in BIP 173,
# and in BIP 350 Bech32 for witness version 0 and Bech32m after; the
# empty `bc1gmk9yu` is Bech32.
# `Bech32.Spec.segwit_strings` proves the same for the strings it lists.
BIP173_VALID = ["A12UEL5L", "a12uel5l",
                "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharacter"
                "sbio1tt5tgs",
                "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw",
                "11qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq"
                "qqqqc8247j",
                "split1checkupstagehandshakeupstreamerranterredcaperred2y9e3w", "?1ezyfcl"]
BIP173_INVALID = ["\x201nwldj5", "\x7f1axkwrx", "\x801eym55h",
                  "an84characterslonghumanreadablepartthatcontainsthenumber1andtheexcludedcharac"
                  "tersbio1569pvx",
                  "pzry9x0s0muk", "1pzry9x0s0muk", "x1b4n0q5v", "li1dgmt3", "de1lg7wt\xff",
                  "A1G7SGD8", "10a06t8", "1qzzfhee"]
BIP350_VALID = ["A1LQFN3A", "a1lqfn3a",
                "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnum"
                "ber11sg7hg6",
                "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx",
                "11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllll"
                "llllludsr8",
                "split1checkupstagehandshakeupstreamerranterredcaperredlc445v", "?1v759aa"]
BIP350_INVALID = ["\x201xj0phk", "\x7f1g6xzxy", "\x801vctc34",
                  "an84characterslonghumanreadablepartthatcontainsthetheexcludedcharactersbioand"
                  "number11d6pts4",
                  "qyrz8wqd2c9m", "1qyrz8wqd2c9m", "y1b0jsk6g", "lt1igcx5c0", "in1muywd",
                  "mm1crxm3i", "au1s5cgom", "M1VUXWEZ", "16plkw9", "1p2gdwpf"]
BIP173_SEGWIT = [
    # the examples of "Segwit address format"
    ("bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4", "bech32"),
    ("tb1qw508d6qejxtdg4y5r3zarvary0c5xw7kxpjzsx", "bech32"),
    ("bc1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3qccfmv3", "bech32"),
    # the test vectors
    ("BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4", "bech32"),
    ("tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7", "bech32"),
    ("bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7k7grplx", "bech32"),
    ("BC1SW50QA3JX3S", "bech32"),
    ("bc1zw508d6qejxtdg4y5r3zarvaryvg6kdaj", "bech32"),
    ("tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy", "bech32"),
    # invalid addresses
    ("tc1qw508d6qejxtdg4y5r3zarvary0c5xw7kg3g4ty", "bech32"),
    ("bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t5", None),
    ("BC13W508D6QEJXTDG4Y5R3ZARVARY0C5XW7KN40WF2", "bech32"),
    ("bc1rw5uspcuh", "bech32"),
    ("bc10w508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kw5rljs90", "bech32"),
    ("BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P", "bech32"),
    ("tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sL5k7", None),
    ("bc1zw508d6qejxtdg4y5r3zarvaryvqyzf3du", "bech32"),
    ("tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3pjxtptv", "bech32"),
    ("bc1gmk9yu", "bech32"),
]
BIP350_SEGWIT = [
    ("BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4", "bech32"),
    ("tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7", "bech32"),
    ("bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y", "bech32m"),
    ("BC1SW50QGDZ25J", "bech32m"),
    ("bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs", "bech32m"),
    ("tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy", "bech32"),
    ("tb1pqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesf3hn0c", "bech32m"),
    ("bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0", "bech32m"),
    # invalid addresses
    ("tc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq5zuyut", "bech32m"),
    ("bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqh2y7hd", "bech32"),
    ("tb1z0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqglt7rf", "bech32"),
    ("BC1S0XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ54WELL", "bech32"),
    ("bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kemeawh", "bech32m"),
    ("tb1q0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq24jc47", "bech32m"),
    ("bc1p38j9r5y49hruaue7wxjce0updqjuyyx0kh56v8s25huc6995vvpql3jow4", None),
    ("BC130XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ7ZWS8R", "bech32m"),
    ("bc1pw5dgrnzv", "bech32m"),
    ("bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v8n0nx0muaewav253zgeav", "bech32m"),
    ("BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P", "bech32"),
    ("tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq47Zagq", None),
    ("bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v07qwwzcrf", "bech32m"),
    ("tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vpggkg4j", "bech32m"),
    ("bc1gmk9yu", "bech32"),
]
VECTORS = ([(s, "bech32") for s in BIP173_VALID] + [(s, None) for s in BIP173_INVALID]
           + [(s, "bech32m") for s in BIP350_VALID] + [(s, None) for s in BIP350_INVALID]
           + BIP173_SEGWIT + BIP350_SEGWIT)

# `Bech32.Spec.encode_vectors`: (variant, HRP, data) and the string, or None.
ENCODE_VECTORS = [
    (("bech32", "a", []), "a12uel5l"), (("bech32m", "a", []), "a1lqfn3a"),
    (("bech32", "abcdef", list(range(32))), "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw"),
    (("bech32m", "abcdef", list(range(31, -1, -1))),
     "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx"),
    (("bech32", "?", []), "?1ezyfcl"),
    (("bech32", "", []), None), (("bech32", "A", []), None), (("bech32", " ", []), None),
    (("bech32", "\x7f", []), None),
    (("bech32", "a", [0] * 82), "a1" + "q" * 82 + raw_encode("bech32", "a", [0] * 82)[-6:]),
    (("bech32", "a", [0] * 83), None),
]

# Characters outside 33 to 126: controls, space, DEL, Latin-1, letters
# whose case mapping leaves ASCII or lands in it (the Kelvin sign, the
# dotted capital I, the long s, the dotless i), and others.
SPECIAL = ["\x00", "\t", "\n", "\r", " ", "\x7f", "\x80", "\xa0", "\xff", "\xe9", "\xc9",
           "\xfc", "\xdf", "\u017f", "\u0131", "\u0130", KELVIN, "\u20ac", "\ufeff",
           "\U0001f600"]
PRINTABLE = [chr(c) for c in range(33, 127)]
LOWER_PRINTABLE = [c for c in PRINTABLE if not is_upper(c)]


def digits_only(variant, hrp, rng):
    """A valid string with HRP `hrp` whose data part is digits only, so
    that the HRP's case alone decides the string's case."""
    digits = [CHARSET.index(c) for c in CHARSET if c.isdigit()]
    while True:
        data = [rng.choice(digits) for _ in range(4)]
        s = raw_encode(variant, hrp, data)
        if s[len(hrp) + 1:].isdigit():
            return s


def short_data(variant, prefix, d):
    """A string whose data part has only `d` characters (fewer than 6)
    and whose checksum still holds: the HRP is `prefix` and 6 - d more
    characters from 96 to 126, whose low bits take the place of the
    missing checksum characters. None if a character would be 127."""
    k = 6 - d
    codes = [ord(c) for c in prefix]
    fixed = [x >> 5 for x in codes] + [3] * k + [0] + [x & 31 for x in codes]
    pm = bech32_polymod(fixed + [0] * 6) ^ CONST[variant]
    sym = [(pm >> 5 * (5 - i)) & 31 for i in range(6)]
    if any(x == 31 for x in sym[:k]):
        return None
    hrp = prefix + "".join(chr(0x60 + x) for x in sym[:k])
    s = hrp + "1" + "".join(CHARSET[x] for x in sym[k:])
    assert bech32_polymod(bech32_hrp_expand([ord(c) for c in hrp]) + sym[k:]) == CONST[variant]
    return s


def edge_decodes():
    rng = random.Random(1)
    out = ["", "1", "11", "111", "a", "a1", "1a", "A1", "?1", "aa", "1qqqqqq", "a1qqqqq",
           "a1qqqqqq", "-", " "]
    for v in VARIANTS:
        # 89, 90 and 91 characters; the separator alone after an HRP.
        for n in (8, 9, 89, 90, 91, 92):
            for hrp, fill in (("a", 0), ("1", 31), ("?", 5)):
                s = raw_encode(v, hrp, [fill] * (n - 8))
                out += [s, s.upper(), s[:-1], s + "q"]
            s = raw_encode(v, "z", [rng.randrange(32) for _ in range(n - 8)])
            out += [s, s.upper()]
        # Far past the limit, and around 1023, the code length of BIP 173.
        for n in (120, 1023, 1024):
            s = raw_encode(v, "a", [rng.randrange(32) for _ in range(n - 8)])
            out += [s, s.upper()]
        # HRPs of 82, 83 and 84 characters.
        for n in (1, 82, 83, 84, 85):
            for data in ([], [7], [1, 2]):
                for hrp in ("x" * n, "".join(rng.choice(LOWER_PRINTABLE) for _ in range(n))):
                    s = raw_encode(v, hrp, data)
                    out += [s, s.upper()]
        # An empty HRP: the separator first.
        for data in ([], [0], [1, 2, 3], [31] * 20):
            s = raw_encode(v, "", data)
            out += [s, s.upper(), "1" + s]
        # Data parts of 5, 6 and 7 characters.
        for hrp in ("a", "abc", "1", "a1"):
            s = raw_encode(v, hrp, [])
            out += [s, s[:-1], s[:len(hrp) + 1] + s[len(hrp) + 2:], s.upper()[:-1], s + "q",
                    hrp + "1", hrp + "1" + s[-5:]]
            s = raw_encode(v, hrp, [9])
            out += [s, s[:-1], s[:-2]]
        # Data parts of 0 to 5 characters whose checksum holds, as in
        # BIP 173's li1dgmt3: the low bits of the HRP's last characters
        # stand in for the rest of the checksum.
        for d in range(6):
            for prefix in ("a", "li", "bc", "x?z", "1"):
                s = short_data(v, prefix, d)
                if s is not None:
                    out += [s, s.upper()]
        # Every printable character that is not a data character, in a
        # data position of a valid string that holds each data
        # character there, in both cases.
        nondata = sorted({c.lower() for c in PRINTABLE} - set(CHARSET))
        for val in range(32):
            s = raw_encode(v, "ab", [val, val])
            k = s.rfind("1") + 1
            for x in nondata:
                t = s[:k] + x + s[k + 1:]
                out += [t, t.upper()]
        # Every printable ASCII character in the HRP, alone, inside, and
        # three times; with the checksum of that HRP, and of its lower
        # case form, in both cases.
        for ch in PRINTABLE:
            for hrp in (ch, "x" + ch + "y", ch * 3):
                out.append(raw_encode(v, hrp, [3, 1]))
                s = raw_encode(v, ascii_lower(hrp), [3, 1])
                out += [s, s.upper()]
        # Characters outside 33 to 126 in the HRP (with the checksum of
        # that HRP), in the data part, first and last.
        base = raw_encode(v, "ab", [0, 1, 2])
        for ch in SPECIAL + [chr(c) for c in (1, 31, 32, 127, 128, 159, 255, 256)]:
            out += [raw_encode(v, ch, []), raw_encode(v, "a" + ch, [4]), ch + base, base + ch,
                    base[:4] + ch + base[5:], base[:1] + ch + base[2:], base[:2] + ch + base[2:]]
        # Mixed case: one letter flipped; HRP and data part in different
        # cases.
        s = raw_encode(v, "abc", [1, 2, 3, 4, 5])
        out += [s, s.upper(), s[:3].upper() + s[3:], s[:3] + s[3:].upper(),
                s[:-1] + s[-1].upper(), s[0].upper() + s[1:], s.upper()[:-1] + s[-1]]
        # The HRP's case alone differing, with a data part of digits.
        for hrp in ("ab", "x", "a?z"):
            s = digits_only(v, hrp, rng)
            out += [s, s.upper(), hrp.upper() + s[len(hrp):], hrp[0].upper() + s[1:]]
        # `1` inside the HRP.
        for hrp in ("1", "11", "a1", "1a", "a1b1", "1" * 20, "1" * 83, "a" * 40 + "1" * 40):
            s = raw_encode(v, hrp, [0, 31] if len(hrp) < 80 else [])
            out += [s, s.upper(), s.replace("1", "", 1)]
        # The Kelvin sign in place of K or k.
        for hrp, data in (("k", [22, 22]), ("bc", [22, 0, 22]), ("kk", [])):
            s = raw_encode(v, hrp, data)
            out += [s.upper().replace("K", KELVIN), s.replace("k", KELVIN),
                    s.upper().replace("K", KELVIN, 1), s.replace("k", KELVIN, 1)]
        # NUL after, before and inside a valid string.
        s = raw_encode(v, "a", [])
        out += [s + "\x00", s + "\x00zzz", "\x00" + s, s[:4] + "\x00" + s[4:], s[:1] + "\x00",
                s.upper() + "\x00a"]
    return list(dict.fromkeys(out))


def edge_encodes():
    out = []
    hrps = (["", "a", "A", "aB", "Ab", "ABC", "?", "1", "11", "a1b", "bc", "tb", "BC"]
            + PRINTABLE + ["x" + c + "y" for c in PRINTABLE]
            + SPECIAL + ["a" + c for c in SPECIAL] + [c + "a" for c in SPECIAL]
            + [chr(c) for c in (1, 31, 32, 127, 128, 159, 255, 256)]
            + ["x" * 82, "x" * 83, "x" * 84, "X" * 83, "1" * 83, "x" * 200])
    for v in VARIANTS:
        for hrp in hrps:
            for data in ([], [0], list(range(32))):
                out.append((v, hrp, data))
        # 89, 90 and 91 characters.
        for n in (80, 81, 82, 83, 84):
            for hrp in ("a", "A", "", "1", KELVIN, "\x00"):
                out.append((v, hrp, [n % 32] * n))
        for h, n in ((82, 0), (82, 1), (83, 0), (83, 1), (84, 0)):
            out.append((v, "x" * h, [9] * n))
            out.append((v, "X" * h, [9] * n))
        out.append((v, "a", [31] * 82))
    return out


GRID_ALPHABET = "qA1?\xfc"


def grid(n):
    for k in range(n + 1):
        for t in itertools.product(GRID_ALPHABET, repeat=k):
            yield "".join(t)


MALFORMED = ["", "decode", "encode", "decode 61 62", "encode bech32 61", "encode bech32 61 - -",
             "DECODE 61", "Decode 61", "encode BECH32 61 -", "encode bech33 61 -",
             "encode bech32M 61 -", "encode - 61 -", "decode 616", "decode 6g", "decode 6A",
             "decode  61", "decode 61 ", " decode 61", "decode ff", "decode c0af",
             "decode eda080", "decode f4908080", "encode bech32 ff -", "encode bech32 6 -",
             "encode bech32 61 20", "encode bech32 61 ff", "encode bech32 61 0",
             "encode bech32 61 1F", "encode bech32 61 0020", "decode --", "encode bech32 - --",
             "decode\t61", "encode bech32 61 -\t", "decode 61\r\r", "decode \xe9"]

# A last line sent with no LF, or with CR LF, and the answer due.
AT_EOF = [(f"decode {hexf('a12uel5l')}", "OK bech32 61 -"),
          ("encode bech32 61 -\r\n", f"OK {hexf('a12uel5l')}"),
          ("decode -\r\n", "FAIL")]

# ---------------------------------------------------------------------
# Random inputs.


def random_hrp(rng):
    """A valid HRP: 1 to 83 characters from 33 to 126, no upper case."""
    r = rng.random()
    if r < 0.4:
        return "".join(rng.choice("abcdefghijklmnopqrstuvwxyz") for _ in range(rng.randint(1, 4)))
    if r < 0.7:
        return "".join(rng.choice(LOWER_PRINTABLE) for _ in range(rng.randint(1, 12)))
    if r < 0.85:
        return "".join(rng.choice("1q?a") for _ in range(rng.randint(1, 6)))
    return "".join(rng.choice(LOWER_PRINTABLE) for _ in range(rng.randint(13, 83)))


def random_valid(rng, room_less=0):
    """A random valid (variant, HRP, data)."""
    hrp = random_hrp(rng)
    room = 90 - 7 - len(hrp) - room_less
    r = rng.random()
    if r < 0.1:
        n = room
    elif r < 0.2:
        n = 0
    else:
        n = rng.randint(0, min(room, rng.choice([8, 40, room])))
    return rng.choice(VARIANTS), hrp, [rng.randrange(32) for _ in range(max(n, 0))]


INSERTED = CHARSET * 3 + "".join(PRINTABLE) + "".join(SPECIAL)


def mutations(rng, s):
    """Every substitution at one sampled position of the valid string
    `s`, an insertion, a deletion, an adjacent swap and a case flip."""
    sep = s.rfind("1")
    up = any(is_upper(c) for c in s)
    i = rng.randrange(len(s))
    if i > sep:
        for c in CHARSET:
            c = c.upper() if up else c
            if c.lower() != s[i].lower():
                yield ("substituted, data part", "d", s[:i] + c + s[i + 1:])
        # Characters that are not data characters, in the string's case.
        for c in rng.sample("1bio", 2):
            c = c.upper() if up else c
            yield ("substituted, other", "d", s[:i] + c + s[i + 1:])
        for c in rng.sample(SPECIAL, 1):
            yield ("substituted, other", "d", s[:i] + c + s[i + 1:])
    elif i == sep:
        for c in rng.sample(PRINTABLE, 4):
            yield ("substituted, separator", "d", s[:i] + c + s[i + 1:])
    else:
        for c in rng.sample(PRINTABLE, 8):
            yield ("substituted, HRP", "d", s[:i] + c + s[i + 1:])
    j = rng.randrange(len(s) + 1)
    c = rng.choice(INSERTED)
    yield ("inserted", "d", s[:j] + (c.upper() if up else c) + s[j:])
    yield ("deleted", "d", s[:i] + s[i + 1:])
    if len(s) > 1:
        j = rng.randrange(len(s) - 1)
        yield ("swapped", "d", s[:j] + s[j + 1] + s[j] + s[j + 2:])
    letters = [j for j, c in enumerate(s) if c.isascii() and c.isalpha()]
    if letters:
        j = rng.choice(letters)
        yield ("case flipped", "d", s[:j] + s[j].swapcase() + s[j + 1:])


def ending_in_p(rng, variant, total=None):
    """A random valid string of the variant whose last character is `p`,
    `total` characters long if given."""
    while True:
        _, hrp, data = random_valid(rng)
        if total is not None:
            hrp = hrp[:max(1, min(len(hrp), total - 9))]
            data = [rng.randrange(32) for _ in range(total - 7 - len(hrp))]
        if not data:
            data = [0]
        for _ in range(200):
            data[-1] = rng.randrange(32)
            s = raw_encode(variant, hrp, data)
            if s[-1] == "p" and len(s) <= 90:
                return s


SMALL_ALPHABET = "qpzlA1?b"


def wild_hrp(rng):
    r = rng.random()
    h = random_hrp(rng)
    if r < 0.2:
        return h.upper()
    if r < 0.3:
        return "".join(c.upper() if rng.random() < 0.5 else c for c in h)
    if r < 0.5:
        j = rng.randrange(len(h) + 1)
        return h[:j] + rng.choice(SPECIAL) + h[j:]
    if r < 0.55:
        return ""
    if r < 0.65:
        return "".join(rng.choice(LOWER_PRINTABLE) for _ in range(rng.randint(80, 100)))
    return h


def inputs(seed, count):
    """(label, kind, item): kind is "d" with a string, or "e" with
    (variant, HRP, data)."""
    for s, _ in VECTORS:
        yield ("BIP vector", "d", s)
    for s, want in VECTORS:
        got = model_decode(s)[0]
        if want is not None and got is not None:
            yield ("BIP vector", "e", got[:2] + (list(got[2]),))
    for x, _ in ENCODE_VECTORS:
        yield ("BIP vector", "e", x)
    for s in edge_decodes():
        yield ("edge", "d", s)
    for x in edge_encodes():
        yield ("edge", "e", x)
    for s in grid(4):
        yield ("grid", "d", s)
    rng = random.Random(seed)
    for _ in range(count):
        v, hrp, data = random_valid(rng)
        yield ("random", "e", (v, hrp, data))
        s = raw_encode(v, hrp, data)
        s = s.upper() if rng.random() < 0.25 else s
        yield ("random", "d", s)
        yield from mutations(rng, s)
        if s.lower().endswith("p"):
            yield ("q inserted, random", "d", s[:-1] + ("QP" if s[-1] == "P" else "qp"))
    for _ in range(max(1, count // 20)):
        for v in VARIANTS:
            for s in (ending_in_p(rng, v), ending_in_p(rng, v, total=90)):
                yield ("random", "d", s)
                yield (f"q inserted, {v}" + (", 90 characters" if len(s) == 90 else ""), "d",
                       s[:-1] + "qp")
    for _ in range(max(1, count // 2)):
        yield ("small alphabet", "d",
               "".join(rng.choice(SMALL_ALPHABET) for _ in range(rng.randint(0, 12))))
        hrp = wild_hrp(rng)
        n = rng.choice([0, rng.randint(0, 20), rng.randint(0, 95)])
        yield ("wild encode", "e",
               (rng.choice(VARIANTS), hrp, [rng.randrange(32) for _ in range(n)]))


# ---------------------------------------------------------------------

def lean_version():
    try:
        out = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, errors="backslashreplace",
                             timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count_arg(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def code(text):
    """`text` as Markdown inline code, whatever backticks it holds."""
    return f"`` {text} ``" if "`" in text else f"`{text}`"


def show(kind, x):
    """A request for the record: strings in Python notation, ASCII only,
    and data values as their characters."""
    if kind == "d":
        return f"decode {ascii(x)}"
    return f"encode {x[0]} {ascii(x[1])} data {ascii(''.join(CHARSET[d] for d in x[2]))}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261026)
    ap.add_argument("--count", type=count_arg, default=30_000)
    ap.add_argument("--no-oracles", action="store_true",
                    help="compare with the model only, as tests/plant_bugs.py does")
    args = ap.parse_args()

    def give_up(why):
        write(["# Test results", "", "- Oracle: none ran", f"- Seed: {args.seed}", "- Inputs: 0",
               f"- Failures: 1 ({why})", ""])
        sys.exit(why)

    try:
        build = subprocess.run(["lake", "build", "bech32"], cwd=ROOT, capture_output=True,
                               text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
        if build.returncode != 0:
            print(build.stdout + build.stderr)
            give_up("`lake build bech32` failed")
    except (OSError, subprocess.SubprocessError) as e:
        give_up(f"`lake build bech32` failed: {e}")

    failures = []
    oracles, left_out = [], []
    for name, setup in ORACLE_SETUPS:
        if args.no_oracles:
            left_out.append((name, "--no-oracles"))
            continue
        try:
            oracles.append(setup())
        except Exception as e:  # any oracle that cannot start is left out, and recorded
            left_out.append((name, str(e).splitlines()[0][:300] if str(e) else type(e).__name__))
            if "SHA-256" in str(e):
                failures.append((f"({name} oracle)", "the files SOURCE.md names", str(e)))
    for name, why in left_out:
        print(f"oracle left out: {name}: {why}")

    items = list(inputs(args.seed, args.count))
    requests = [(f"decode {hexf(x)}" if k == "d" else f"encode {x[0]} {hexf(x[1])} {valf(x[2])}")
                for _, k, x in items]
    lines = [r + ("\r\n" if i % 7 == 6 else "\n") for i, r in enumerate(requests)]
    malformed_at = len(lines)
    lines += [m + "\n" for m in MALFORMED]
    out, problem = run_lines([str(EXE), "serve"], lines)
    if problem:
        failures.append(("(whole run)", "a clean run", problem))
    if len(out) != len(lines):
        failures.append(("(whole run)", f"{len(lines)} answers", f"{len(out)} answers"))
        out += [""] * (len(lines) - len(out))
    malformed_right = sum(1 for a in out[malformed_at:] if a == "error")
    for m, a in zip(MALFORMED, out[malformed_at:]):
        if a != "error":
            failures.append((f"request {m!r}", "error", a))
    eof_right = 0
    for req, want in AT_EOF:
        got, problem = run_lines([str(EXE), "serve"], [req], timeout=60)
        if got == [want] and not problem:
            eof_right += 1
        else:
            failures.append((req + " (at end of input)", want, f"{got} {problem or ''}".strip()))

    lean = [parse_answer(k, a) for (_, k, _), a in zip(items, out)]

    # Against the model.
    model, why_not = [], {}
    differ_model = 0
    for (label, kind, x), got in zip(items, lean):
        if kind == "d":
            want, why = model_decode(x)
        else:
            want, why = model_encode(*x)
        model.append(want)
        if why is not None:
            key = (kind, why)
            why_not[key] = why_not.get(key, 0) + 1
        if got != want:
            differ_model += 1
            failures.append((show(kind, x)[:200], repr(want)[:160], repr(got)[:160]))

    # The model on the BIP vectors, as a check of the model.
    vectors_right = sum(1 for s, want in VECTORS
                        if (model_decode(s)[0] or (None,))[0] == want)
    for s, want in VECTORS:
        if (model_decode(s)[0] or (None,))[0] != want:
            failures.append((f"the model on BIP vector {s!r}", repr(want), repr(model_decode(s))))
    for x, want in ENCODE_VECTORS:
        if model_encode(*x)[0] != want:
            failures.append((f"the model on {show('e', x)}", repr(want), repr(model_encode(*x))))

    # The proved claims, counted.
    subs = [g for (label, _, _), g in zip(items, lean) if label == "substituted, data part"]
    subs_decoding = sum(1 for g in subs if g is not None)
    if subs_decoding:
        failures.append(("single substitutions in the data part", "none decode",
                         f"{subs_decoding} decode"))
    qcount = {}
    for (label, _, _), g in zip(items, lean):
        if label.startswith("q inserted, bech32"):
            n, ok = qcount.get(label, (0, 0))
            qcount[label] = (n + 1, ok + (g is not None and g[0] == "bech32"))
    for label, (n, ok) in qcount.items():
        want = n if label == "q inserted, bech32" else 0
        stays = sum(1 for (lb, _, _), g in zip(items, lean) if lb == label and g is not None)
        if ok != want or (want == 0 and stays):
            failures.append((label, f"{want} of {n} valid", f"{ok} of {n} valid as Bech32, "
                             f"{stays} valid"))

    # Against the oracles.
    oracle_answers = {}
    for o in list(oracles):
        try:
            oracle_answers[o.name] = o.answers(items)
        except (RuntimeError, OSError) as e:
            failures.append((f"({o.name} oracle run)", "a clean run", str(e)[:300]))
            oracles.remove(o)
    names = [o.name for o in oracles]
    agree = {o: 0 for o in names}
    named = {o: {} for o in names}
    for i, (label, kind, x) in enumerate(items):
        got = lean[i]
        for o in names:
            theirs = oracle_answers[o][i]
            if theirs == got:
                agree[o] += 1
                continue
            reason = difference_reason(o, kind, x, got, theirs)
            if reason is None:
                failures.append((f"{o}: {show(kind, x)}"[:200], repr(got)[:160],
                                 repr(theirs)[:160]))
            else:
                key = (reason, "decoding" if kind == "d" else "encoding")
                n, example = named[o].get(key, (0, None))
                named[o][key] = (n + 1, example or show(kind, x))

    by_label = {}
    for label, kind, _ in items:
        key = f"{label} {'decode' if kind == 'd' else 'encode'}"
        by_label[key] = by_label.get(key, 0) + 1
    decodes = [(x, g) for (_, k, x), g in zip(items, lean) if k == "d"]
    valid = {v: sum(1 for _, g in decodes if g is not None and g[0] == v) for v in VARIANTS}
    encodes = [(x, g) for (_, k, x), g in zip(items, lean) if k == "e"]
    written = sum(1 for _, g in encodes if g is not None)

    def counts(kind):
        return ", ".join(f"{why} {n}" for (k, why), n in
                         sorted(why_not.items(), key=lambda kv: -kv[1]) if k == kind)

    def q_line(v):
        a = qcount.get(f"q inserted, {v}", (0, 0))
        b = qcount.get(f"q inserted, {v}, 90 characters", (0, 0))
        sa = sum(1 for (lb, _, _), g in zip(items, lean)
                 if lb == f"q inserted, {v}" and g is not None)
        sb = sum(1 for (lb, _, _), g in zip(items, lean)
                 if lb == f"q inserted, {v}, 90 characters" and g is not None)
        return (f"{v}: {sa} of {a[0]} that fit in 90 characters, {sb} of {b[0]} of 90 "
                f"characters before the insertion")

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Lean: {lean_version()}",
        "- Oracle: the model of BIP 173 and BIP 350, `model_decode` and `model_encode` in "
        "`tests/run_tests.py`, and the implementations below",
    ]
    lines += [f"- {o.name}: {o.version}" for o in oracles]
    lines += [
        "- Oracles left out: " + ("; ".join(f"{n} ({why})" for n, why in left_out)
                                  if left_out else "none"),
        f"- Seed: {args.seed}",
        f"- Inputs: {len(items)}",
        "- By kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())),
        f"- Answers that differ from the model: {differ_model}",
        f"- Strings decoded: {len(decodes)}, of which {valid['bech32']} are valid Bech32, "
        f"{valid['bech32m']} valid Bech32m, and {len(decodes) - sum(valid.values())} not valid",
        f"- Why the model refuses those: {counts('d')}",
        f"- Encodings asked for: {len(encodes)}, of which {written} are written and "
        f"{len(encodes) - written} refused: {counts('e')}",
        f"- BIP 173 and BIP 350 test strings the model reads as expected, the segwit address "
        f"lists as strings: {vectors_right} of {len(VECTORS)}",
        f"- Single substitutions in the data part of a valid string that still decode: "
        f"{subs_decoding} of {len(subs)}",
        "- Valid strings ending in p that stay valid with q inserted before the p: "
        + "; ".join(q_line(v) for v in VARIANTS),
        "- Agreement with each oracle over all inputs: "
        + ", ".join(f"{o} {agree[o]} of {len(items)}" for o in names),
        f"- Malformed requests answered `error`: {malformed_right} of {len(MALFORMED)}",
        f"- Requests ending in CR LF: every seventh, {len(requests) // 7}",
        f"- Last lines sent alone, with no LF or with CR LF, answered right: {eof_right} of "
        f"{len(AT_EOF)}",
        f"- Failures: {len(failures)}",
        "",
        "## Where the oracles differ",
        "",
        "Each disagreement is counted under the reason the model confirms, with the first "
        "input that showed it.",
        "",
    ]
    for o in names:
        lines.append(f"### {o}")
        lines.append("")
        if not named[o]:
            lines.append("No disagreement.")
        for (reason, kind), (n, example) in sorted(named[o].items(), key=lambda kv: -kv[1][0]):
            lines.append(f"- {reason}, {kind}: {n}; for example {code(example[:240])}")
        lines.append("")
    if failures:
        lines += ["## Failures", ""]
        lines += [f"- {code(req)}: expected {code(want)}, got {code(got)}"
                  for req, want, got in failures[:50]]
        lines.append("")
    write(lines)
    print(f"{len(items)} inputs, {len(oracles)} oracles, {len(failures)} failures; results in "
          f"{RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
