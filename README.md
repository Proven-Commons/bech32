# bech32: Bech32 and Bech32m strings (BIP 173, BIP 350), proved

Bech32 and Bech32m write a short human-readable label and a list of 5-bit values as one string with a checksum, such as `bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4`. Segwit and taproot addresses use them, and so do Lightning invoices and many other formats. A string read wrongly can send money where nobody can spend it. This library reads and writes the strings in Lean. Machine-checked proofs show:

- The decoder accepts exactly the strings BIP 173 and BIP 350 allow, and reads each one in exactly one way.
- Decoding an encoding gives back what was encoded, and every valid string is an encoding, up to upper case.
- The encoder writes lower case only, as BIP 173 requires.
- A single changed character in the data part is always caught, whichever variant either string is.
- Inserting `q` before a final `p` leaves a Bech32 string valid, which is the weakness BIP 350 was written to fix, and always breaks a Bech32m string.

It is tested against a model of the BIPs and five other implementations: sipa's reference code in Python and C, npm `bech32`, Go's `btcutil/bech32`, and Rust's `bech32`. The record is in `tests/TEST-RESULTS.md`: 1,012,996 inputs, 0 failures. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean:

- `Bech32.encode : Variant → String → List (Fin 32) → Option String`
- `Bech32.decode : String → Option (Variant × String × List (Fin 32))`

`Variant` is `.bech32` or `.bech32m`. `decode` gives the human-readable part in lower case and the data without the checksum. `SPEC.md` says what each one does, and when `encode` fails.

## What is proved

The statements are in `Spec.lean`, the definitions they use in `Spec/Defs.lean`, and the proofs in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| `decode s` succeeds exactly when `s` is valid by BIP 173 and BIP 350, and then gives its variant, its human-readable part in lower case, and its data. `Spec.Valid` states the rules: at most 90 characters, each from 33 to 126, not mixed case, a human-readable part of 1 to 83 characters, the separator, at least 6 data characters, and the checksum of BIP 173's own code giving 1 (Bech32) or `0x2bc830a3` (Bech32m). | `Spec.decode_iff` |
| `encode` succeeds exactly when the human-readable part is not empty, has only characters from 33 to 126 and no upper case letter, and the string fits in 90 characters. | `Spec.encode_isSome` |
| Decoding an encoding gives back the variant, the human-readable part and the data. | `Spec.decode_encode` |
| Every string `decode` accepts is what `encode` writes, in lower case. | `Spec.encode_decode` |
| An encoding has no upper case letter. | `Spec.encode_lower` |
| Two strings that, in lower case, differ in one character of the data part never both decode, under either variant. | `Spec.one_substitution` |
| Inserting `q` before a final `p` keeps a Bech32 string valid, if it still fits. | `Spec.insert_q_bech32` |
| The same insertion never leaves a Bech32m string valid. | `Spec.insert_q_bech32m` |
| Every test vector of BIP 173 and BIP 350, valid and invalid; the segwit address vectors, read as strings; and encodings at the limits. | `Spec.bip173_valid`, `Spec.bip173_invalid`, `Spec.bip350_valid`, `Spec.bip350_invalid`, `Spec.segwit_strings`, `Spec.encode_vectors` |

The command-line tool in `Main.lean` answers requests with these functions directly.

## What is not proved

- **Segwit addresses.** The witness version, the program length, the conversion between bytes and 5-bit values and its padding, and which variant each witness version needs are a later slice. Most of the addresses BIP 350 lists as invalid are valid strings, and `Spec.segwit_strings` says which.
- **Errors in more than one character.** BIP 173 says the checksum catches any error in at most 4 characters. Only the one-character case in the data part is proved here. An error in the human-readable part can change two checksum values at once, and `Spec.one_substitution` does not cover it.
- **Longer strings.** Some formats, such as Lightning invoices, use Bech32 past 90 characters. This library keeps the 90-character limit of BIP 173.
- **Reading requests and printing answers in `Main.lean`.** The differential tests cover them.

## Where other implementations differ

The tests compare every answer with five other implementations and count each disagreement under its reason, confirmed against the model. On strings of at most 90 characters their decoders agree with this one, with two exceptions: npm's reading of the Kelvin sign and sipa C's reading of NUL, both below. Most differences are in what their encoders let through.

- **npm `bech32` 2.0.0 accepts a character outside ASCII.** It lower-cases with Unicode rules before it checks a string, so the Kelvin sign U+212A reads as `k`. It decodes `K1KKS7FG6D`, written with Kelvin signs, to the same prefix and data as `k1kks7fg6d`, and encodes the HRP `K` (Kelvin) as `k18duse0`. BIP 173 allows only characters 33 to 126, and this library rejects both.
- **No 90-character limit.** Rust's `bech32` 0.11.1 decodes and encodes strings up to the code length, 1023 characters. Go's `btcutil/bech32` and sipa's Python reference encode past 90 characters.
- **Encoders that check less than BIP 173 asks:**
  - an empty HRP is written by sipa's Python and C references, npm and Go, which gives `10a06t8`, a string BIP 173 lists as invalid;
  - an upper case HRP is written as it is by sipa's Python reference, which gives strings such as `A1G7SGD8`, also listed as invalid, and is lower-cased by npm, Go and Rust;
  - HRP characters outside 33 to 126 are written by sipa's Python reference and Go; Go also lower-cases them with Unicode rules and checksums their UTF-8 bytes.

  This library refuses all of these: `Spec.encode_isSome` says exactly what it writes.
- **C strings.** sipa's C reference reads its input up to the first NUL.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about, such as natural number arithmetic and bitwise operations, and the conversion between strings and lists.
- The operating system and hardware it runs on.
- For the tests only: the model in `tests/run_tests.py`, and the implementations it compares against. The record names their versions.

This project has no dependencies beyond Lean itself.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), Python 3 and a C compiler. The oracles also need Node and npm, Go, and Rust's cargo; the test script leaves out any it cannot build, and the record names them.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
python3 tests/plant_bugs.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

The test script builds the tool and the oracles, and runs these inputs:

- every string of BIP 173 and BIP 350, with their encodings;
- edge cases at the length limits, every printable character in the HRP, characters outside the range, mixed case, and `1` inside the HRP;
- every string of up to four characters over a small alphabet;
- random valid strings of both variants, with substitutions in the HRP, the separator and the data part, insertions, deletions, swaps of neighbours, case flips, and `q` inserted before a final `p`;
- random strings and encodings, from a recorded seed;
- malformed requests and CR LF line endings.

It then rewrites `tests/TEST-RESULTS.md`, which also counts the substitutions and insertions as checks of the proved claims. `tests/plant_bugs.py` plants ten bugs in a copy of the code, one at a time, and records in `tests/PLANTED-BUGS.md` how many failures the tests report for each. Every bug must be caught, and each of them also breaks a proof.

## Layout

- `Bech32/Basic.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from BIP 173 and BIP 350.
- `Proofs.lean` and `Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/`: the differential tests, the oracles, and the planted bugs.
