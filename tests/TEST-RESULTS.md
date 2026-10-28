# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Oracle: the model of BIP 173 and BIP 350, `model_decode` and `model_encode` in `tests/run_tests.py`, and the implementations below
- sipa Python: `bech32_decode` and `bech32_encode` of `ref/python/segwit_addr.py`, sipa/bech32 commit 7a7d7ab158db7078a333384e0e918c90dbc42917, SHA-256 2884ce04a36c8374c4249177cd90e91e545ac73b5c9260307bbeb74ae2e9de0f, on Python 3.13.17
- sipa C: `bech32_decode` and `bech32_encode` of `ref/c/segwit_addr.c`, sipa/bech32 commit 7a7d7ab158db7078a333384e0e918c90dbc42917, SHA-256 aa73529c41142d2a9fed384676910943692236eda2ec583f96a95b5283c3042d, compiled with cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0
- npm: bech32 2.0.0 (bitcoinjs), integrity sha512-LcknSilhIGatDAsY1ak2I8VtGaHNhgMSYVxFrGLXv+xLHytaKZKcaUJJUE7qmBr7h33o5YQwP55pMI0xmkpJwg==, on Node v22.22.0
- Go: package bech32 of github.com/btcsuite/btcd/btcutil v1.2.0 (h1:p3+S2g3Q+7G5NOh4Ji+2UrBOrg5Z0Q4ykzShWG1Dhgs=), built with go version go1.24.7 linux/amd64
- Rust: bech32 0.11.1 (rust-bitcoin), checksum 32637268377fc7b10a8c6d51de3e7fba1ce5dd371a96e342b34e6078db558e7f, built with rustc 1.97.0 (2d8144b78 2026-07-07)
- Oracles left out: none
- Seed: 20261026
- Inputs: 1016772
- By kind: BIP vector decode 82, BIP vector encode 63, case flipped decode 30000, deleted decode 30000, edge decode 6528, edge encode 1732, grid decode 781, inserted decode 30000, q inserted, bech32 decode 1334, q inserted, bech32, 90 characters decode 1666, q inserted, bech32m decode 1348, q inserted, bech32m, 90 characters decode 1652, q inserted, random decode 974, random decode 36000, random encode 30000, small alphabet decode 15000, substituted, HRP decode 60464, substituted, data part decode 655526, substituted, other decode 63438, substituted, separator decode 5184, swapped decode 30000, wild encode encode 15000
- Answers that differ from the model: 0
- Strings decoded: 969977, of which 21069 are valid Bech32, 19502 valid Bech32m, and 929406 not valid
- Why the model refuses those: the checksum 780359, a character that is not a data character 63312, mixed case 58085, no separator 9277, a data part of fewer than 6 characters 8921, longer than 90 characters 6844, an HRP of no characters or more than 83 1505, an HRP character outside 33 to 126 1103
- Encodings asked for: 46795, of which 36383 are written and 10412 refused: an upper case letter in the HRP 4256, an HRP character outside 33 to 126 3497, longer than 90 characters 1853, an empty HRP 806
- BIP 173 and BIP 350 test strings the model reads as expected, the segwit address lists as strings: 82 of 82
- Single substitutions in the data part of a valid string that still decode: 0 of 655526
- Valid strings ending in p that stay valid with q inserted before the p: bech32: 1334 of 1334 that fit in 90 characters, 0 of 1666 of 90 characters before the insertion; bech32m: 0 of 1348 that fit in 90 characters, 0 of 1652 of 90 characters before the insertion
- Agreement with each oracle over all inputs: sipa Python 1006360 of 1016772, sipa C 1015818 of 1016772, npm 1011914 of 1016772, Go 1006360 of 1016772, Rust 1011051 of 1016772
- Malformed requests answered `error`: 35 of 35
- Requests ending in CR LF: every seventh, 145253
- Last lines sent alone, with no LF or with CR LF, answered right: 3 of 3
- Failures: 0

## Where the oracles differ

Each disagreement is counted under the reason the model confirms, with the first input that showed it.

### sipa Python

- sipa Python writes an upper case HRP as it is, with its checksum, encoding: 3880; for example `encode bech32 'A' data ''`
- sipa Python writes HRP characters outside 33 to 126, encoding: 3237; for example `encode bech32 ' ' data ''`
- sipa Python has no 90-character limit, encoding: 1853; for example `encode bech32 'a' data 'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'`
- sipa Python writes an empty HRP, encoding: 778; for example `encode bech32 '' data ''`
- sipa Python has no 90-character limit; writes an upper case HRP as it is, with its checksum, encoding: 376; for example `encode bech32 'XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX' data 'q'`
- sipa Python has no 90-character limit; writes HRP characters outside 33 to 126, encoding: 260; for example `encode bech32 '\u212a' data 'nnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn'`
- sipa Python writes an empty HRP; has no 90-character limit, encoding: 28; for example `encode bech32 '' data '555555555555555555555555555555555555555555555555555555555555555555555555555555555555'`

### sipa C

- sipa C writes an empty HRP, encoding: 778; for example `encode bech32 '' data ''`
- sipa C reads the HRP as a C string, which ends at the first NUL, encoding: 162; for example `encode bech32 '\x00' data ''`
- sipa C reads a C string, which ends at the first NUL, decoding: 14; for example `decode 'ab1qpzfg27ph\x00'`

### npm

- npm lower-cases the HRP, encoding: 3880; for example `encode bech32 'A' data ''`
- npm writes an empty HRP, encoding: 778; for example `encode bech32 '' data ''`
- npm lower-cases the HRP with Unicode rules, which turn the Kelvin sign into k, encoding: 179; for example `encode bech32 '\u212a' data ''`
- npm lower-cases with Unicode rules, so the Kelvin sign U+212A reads as k, decoding: 21; for example `decode '\u212a1\u212a\u212aS7FG6D'`

### Go

- Go lower-cases the HRP, encoding: 3880; for example `encode bech32 'A' data ''`
- Go writes HRP characters outside 33 to 126, lower-cased with Unicode rules, with the checksum over their UTF-8 bytes, encoding: 3237; for example `encode bech32 ' ' data ''`
- Go has no 90-character limit, encoding: 1853; for example `encode bech32 'a' data 'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'`
- Go writes an empty HRP, encoding: 778; for example `encode bech32 '' data ''`
- Go has no 90-character limit; lower-cases the HRP, encoding: 376; for example `encode bech32 'XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX' data 'q'`
- Go has no 90-character limit; writes HRP characters outside 33 to 126, lower-cased with Unicode rules, with the checksum over their UTF-8 bytes, encoding: 260; for example `encode bech32 '\u212a' data 'nnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn'`
- Go writes an empty HRP; has no 90-character limit, encoding: 28; for example `encode bech32 '' data '555555555555555555555555555555555555555555555555555555555555555555555555555555555555'`

### Rust

- Rust lower-cases the HRP, encoding: 2985; for example `encode bech32 'A' data ''`
- Rust has no 90-character limit (its limit is the code length, 1023), decoding: 1781; for example `decode 'a1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqql0ccdy'`
- Rust has no 90-character limit, encoding: 675; for example `encode bech32 'a' data 'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'`
- Rust has no 90-character limit; lower-cases the HRP, encoding: 280; for example `encode bech32 'XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX' data 'q'`
