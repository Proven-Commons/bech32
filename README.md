# bech32: Bech32 and Bech32m strings (BIP 173, BIP 350), proved

Bech32 and Bech32m write a short human-readable label and a list of 5-bit values as one string with a checksum, such as `bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4`. Segwit and taproot addresses use them, and so do Lightning invoices and many other formats. A string read wrongly can send money where nobody can spend it. This library reads and writes the strings in Lean. Machine-checked proofs show:

- The decoder accepts exactly the strings BIP 173 and BIP 350 allow, and reads each one in exactly one way.
- Decoding an encoding gives back what was encoded, and every valid string is an encoding, up to upper case.
- The encoder writes lower case only, as BIP 173 requires.
- A single changed character in the data part is always caught, whichever variant either string is.
- Inserting `q` before a final `p` leaves a Bech32 string valid, which is the weakness BIP 350 was written to fix, and always breaks a Bech32m string.

It is tested against a model of the BIPs and five other implementations. `tests/TEST-RESULTS.md` has the record. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

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

TESTS-PENDING

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

TESTS-PENDING

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
