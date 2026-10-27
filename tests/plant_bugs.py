#!/usr/bin/env python3
"""Check that the differential tests catch planted bugs.

Each bug is a one-line change to Bech32/Basic.lean. The script copies
the project to a temporary folder, plants one bug at a time, runs
tests/run_tests.py there with a small count and without the oracles,
and records how many failures the tests report. So every failure
counted is the tool disagreeing with the model of the BIPs, or with a
BIP vector; an oracle that crashes or times out cannot pass for a
catch. Every planted bug must give at least one failure. The unchanged
copy must give none. A bug that stops the executable from building is
not a catch: the tests then give up, and the bug counts as missed, as
does any run that gives up or dies. The tests build only the
executable, so a bug that breaks a proof still runs.

    python3 tests/plant_bugs.py [--count N]

The script writes tests/PLANTED-BUGS.md and exits non-zero if any bug
goes uncaught.
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "tests" / "PLANTED-BUGS.md"
CODE = "Bech32/Basic.lean"

# (what the bug does, the line as written, the line with the bug)
BUGS = [
    ("one generator constant is wrong",
     "let chk := if b &&& 8 = 0 then chk else chk ^^^ 0x3d4233dd",
     "let chk := if b &&& 8 = 0 then chk else chk ^^^ 0x3d4233dc"),
    ("the checksum keeps 26 bits before the shift, not 25",
     "let chk := ((chk &&& 0x1ffffff) <<< 5) ^^^ v",
     "let chk := ((chk &&& 0x3ffffff) <<< 5) ^^^ v"),
    ("a string of 91 characters is allowed",
     "if 90 < cs.length || !cs.all isPrintable || (cs.any isUpper && cs.any isLower) then none",
     "if 91 < cs.length || !cs.all isPrintable || (cs.any isUpper && cs.any isLower) then none"),
    ("the HRP may be empty",
     "if hrp.isEmpty || rest.length < 6 then none",
     "if rest.length < 6 then none"),
    ("mixed case is allowed",
     "if 90 < cs.length || !cs.all isPrintable || (cs.any isUpper && cs.any isLower) then none",
     "if 90 < cs.length || !cs.all isPrintable then none"),
    ("the first 1 is taken as the separator",
     "match cs.reverse.idxOf? '1' with",
     "match (cs.idxOf? '1').map (cs.length - 1 - ·) with"),
    ("the Bech32m constant has two digits swapped",
     "| .bech32m => 0x2bc830a3",
     "| .bech32m => 0x2bc803a3"),
    ("the HRP expansion leaves out the zero",
     "hrp.map (fun c => c.toNat >>> 5) ++ [0] ++ hrp.map (fun c => c.toNat &&& 31)",
     "hrp.map (fun c => c.toNat >>> 5) ++ hrp.map (fun c => c.toNat &&& 31)"),
    ("the HRP is checksummed in upper case",
     "match variantOf hrp (data.map (·.val)) with",
     "match variantOf (hrp.map Char.toUpper) (data.map (·.val)) with"),
    ("two characters of the charset are swapped",
     'def charset : List Char := "qpzry9x8gf2tvdw0s3jn54khce6mua7l".toList',
     'def charset : List Char := "qpzry98xgf2tvdw0s3jn54khce6mua7l".toList'),
    ("o is read as the digit 0",
     "let i := charset.idxOf c",
     "let i := charset.idxOf (if c = 'o' then '0' else c)"),
    ("a data part of 5 characters is allowed",
     "if hrp.isEmpty || rest.length < 6 then none",
     "if hrp.isEmpty || rest.length < 5 then none"),
    ("the encoder writes 91 characters",
     "if h.isEmpty || !h.all (fun c => isPrintable c && !isUpper c) || 90 < h.length + 7 + data.length then",
     "if h.isEmpty || !h.all (fun c => isPrintable c && !isUpper c) || 91 < h.length + 7 + data.length then"),
    ("the encoder writes an upper case HRP",
     "if h.isEmpty || !h.all (fun c => isPrintable c && !isUpper c) || 90 < h.length + 7 + data.length then",
     "if h.isEmpty || !h.all (fun c => isPrintable c) || 90 < h.length + 7 + data.length then"),
    ("the encoder writes an empty HRP",
     "if h.isEmpty || !h.all (fun c => isPrintable c && !isUpper c) || 90 < h.length + 7 + data.length then",
     "if !h.all (fun c => isPrintable c && !isUpper c) || 90 < h.length + 7 + data.length then"),
]


def failures(copy, count):
    """The failures a run of the tests reports, or None, with the run's
    output, when it reports none: the code did not build, or the run did
    not finish. A run that dies writes no record, so the old one is
    removed first rather than read again."""
    record = copy / "tests" / "TEST-RESULTS.md"
    record.unlink(missing_ok=True)
    run = subprocess.run([sys.executable, "tests/run_tests.py", "--count", str(count),
                          "--no-oracles"],
                         cwd=copy, capture_output=True, text=True)
    out = run.stdout + run.stderr
    if not record.exists():
        return None, f"no record written, exit status {run.returncode}\n{out}"
    m = re.search(r"^- Failures: (\d+)(.*)$", record.read_text(encoding="utf-8"), re.M)
    if m is None or m.group(2).strip():
        return None, out  # the run gave up, for example the bug did not build: not a catch
    n = int(m.group(1))
    if run.returncode != (1 if n else 0):
        return None, f"{n} failures but exit status {run.returncode}\n{out}"
    return n, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=1000)
    args = ap.parse_args()
    rows, missed = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "bech32"
        shutil.copytree(ROOT, copy, symlinks=True,
                        ignore=shutil.ignore_patterns("PLANTED-BUGS.md", "__pycache__"))
        code = copy / CODE
        original = code.read_text(encoding="utf-8")
        n, err = failures(copy, args.count)
        rows.append(("none", n))
        if n != 0:
            missed += 1
        print(f"none: {n} failures" + (" (did not build or did not finish)" if err else ""))
        for what, line, bug in BUGS:
            if original.count(line) != 1:
                sys.exit(f"{CODE} no longer holds, once, the line for {what!r}: {line}")
            code.write_text(original.replace(line, bug), encoding="utf-8")
            n, err = failures(copy, args.count)
            code.write_text(original, encoding="utf-8")
            rows.append((what, n))
            if not n:
                missed += 1
            print(f"{what}: {n} failures" + (" (did not build or did not finish)" if err else ""))
    lines = ["# Planted bugs", "",
             "Written by `tests/plant_bugs.py`. Each bug is a one-line change to "
             f"`{CODE}`, tested with `tests/run_tests.py --count {args.count} --no-oracles`, "
             "so each failure is the tool disagreeing with the model or a BIP vector. "
             "Every bug must give failures, and the unchanged code none. A bug that does not "
             "build, or a run that gives up, counts as missed.", "",
             "| Planted bug | Failures |", "|---|---|"]
    lines += [f"| {what} | {'did not build or did not finish' if n is None else n} |" for what, n in rows]
    lines += ["", f"Bugs caught: {sum(1 for what, n in rows[1:] if n)} of {len(BUGS)}", ""]
    RECORD.write_text("\n".join(lines), encoding="utf-8")
    return 1 if missed else 0


if __name__ == "__main__":
    sys.exit(main())
