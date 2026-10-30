# Specification: bech32

Bech32 (BIP 173, https://github.com/bitcoin/bips/blob/master/bip-0173.mediawiki) and Bech32m (BIP 350, https://github.com/bitcoin/bips/blob/master/bip-0350.mediawiki) write a short human-readable label and a list of 5-bit values as one string with a checksum. Segwit and taproot addresses use them, and so do Lightning invoices and many other formats. This library reads and writes the strings. It does not read segwit addresses (witness version, program length, the conversion from bytes to 5-bit values); that is a later slice.

A reviewer who did not write this specification approves it. The approval also covers `Bech32/Spec.lean`, `Bech32/Spec/Defs.lean`, and the other files `bar.toml` lists.

## The format

A string has three parts:

- **The human-readable part** (HRP): 1 to 83 characters, each US-ASCII in the range 33 to 126.
- **The separator**, `1`. The HRP may contain `1` too; the last `1` in the string is the separator.
- **The data part**: at least 6 characters from `qpzry9x8gf2tvdw0s3jn54khce6mua7l`, which stand for the values 0 to 31 in that order. The last 6 are the checksum.

The whole string is at most 90 characters, and it is all lower case or all upper case: a decoder must not accept a mixed-case string. The lower case form is used for the checksum.

**The checksum.** BIP 173 defines it by code, which it makes normative: `bech32_polymod` over the values of `bech32_hrp_expand(hrp)` (the high bits of each HRP character, a zero, then the low bits) followed by the data values. A Bech32 string gives 1. BIP 350 changed only that constant: a Bech32m string gives `0x2bc830a3`. No string gives both, so the checksum also says which variant a string is.

`Bech32/Spec/Defs.lean` copies the BIP's checksum code line for line, and states the rules above as `Bech32.Spec.Valid`.

## Decoding

`decode s` gives the variant, the HRP in lower case, and the data values without the checksum. It fails unless `s` is valid by the rules above. Since the separator is the last `1` and no data character is `1`, a valid string has exactly one reading.

## Encoding

`encode v hrp data` writes the HRP, the separator, the data characters and the six checksum characters of variant `v`, all in lower case, as BIP 173 requires of encoders. It fails when:

- the HRP is empty;
- the HRP has a character outside 33 to 126;
- the HRP has an upper case letter, since writing it would give a mixed-case or upper case string whose HRP is not the one given;
- the string would be longer than 90 characters.

## What must always hold

Each property is a theorem in `Bech32/Spec.lean`, under the name given.

| Property | Theorem |
|----------|---------|
| `decode s` succeeds exactly for the strings the BIP rules allow, and gives their variant, HRP and data. | `Bech32.Spec.decode_iff` |
| `encode` succeeds exactly when the HRP is valid and in lower case and the string fits in 90 characters. | `Bech32.Spec.encode_isSome` |
| Decoding an encoding gives back the variant, the HRP and the data. | `Bech32.Spec.decode_encode` |
| What `decode` accepts, `encode` writes back in lower case. | `Bech32.Spec.encode_decode` |
| An encoding has no upper case letter. | `Bech32.Spec.encode_lower` |
| Two strings that, in lower case, differ in one character of the data part, where each holds a data character, never both decode, whichever variant each has. | `Bech32.Spec.one_substitution` |
| A data character changed to `1` moves the separator, and both strings can be valid. | `Bech32.Spec.separator_substitution` |
| Inserting `q` before a final `p` keeps a Bech32 string valid: the weakness BIP 350 fixes. | `Bech32.Spec.insert_q_bech32` |
| The same insertion never leaves a Bech32m string valid. | `Bech32.Spec.insert_q_bech32m` |
| The test vectors of BIP 173 and BIP 350, valid and invalid, and the segwit address vectors read as strings. | `Bech32.Spec.bip173_valid`, `Bech32.Spec.bip173_invalid`, `Bech32.Spec.bip350_valid`, `Bech32.Spec.bip350_invalid`, `Bech32.Spec.segwit_strings` |
| Encodings of BIP strings, and the limits of `encode`. | `Bech32.Spec.encode_vectors` |

`Bech32.Spec.decode_iff` fixes `decode` on every string. `Bech32.Spec.encode_decode` and `Bech32.Spec.decode_encode` then fix `encode` on every input it accepts, and `Bech32.Spec.encode_isSome` says which inputs those are.

BIP 173 also says the checksum detects any error that affects at most 4 characters, among strings of one variant. This slice proves the one-character case for the data part, among data characters, under both variants together. The rest is neither proved nor tested here. A decoder that accepts both variants detects fewer errors: BIP 350 notes that a valid Bech32 string and a valid Bech32m string can differ in as few as 3 characters. A change to `1` moves the separator, and is not covered at all (`Bech32.Spec.separator_substitution`).

## The command-line tool

The command-line tool in `Main.lean` has these modes:

- `bech32 decode STRING` prints the variant, the HRP and the data values, or exits with 1 when the string is not valid.
- `bech32 encode bech32|bech32m HRP VALUES` prints the string, or exits with 1 when it cannot be written.
- `bech32 serve` answers requests from the differential tests, one per line. The header comment of `Main.lean` gives the protocol.

Every answer comes from `encode` and `decode`.
