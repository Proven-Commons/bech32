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
- Inputs: 1012996
- By kind: BIP vector decode 82, BIP vector encode 63, case flipped decode 29999, deleted decode 30000, edge decode 1810, edge encode 1732, grid decode 781, inserted decode 30000, q inserted, bech32 decode 1337, q inserted, bech32, 90 characters decode 1663, q inserted, bech32m decode 1349, q inserted, bech32m, 90 characters decode 1651, q inserted, random decode 967, random decode 36000, random encode 30000, small alphabet decode 15000, substituted, HRP decode 60264, substituted, data part decode 656611, substituted, other decode 63543, substituted, separator decode 5144, swapped decode 30000, wild encode encode 15000
- Answers that differ from the model: 0
- Strings decoded: 966201, of which 21199 are valid Bech32, 19302 valid Bech32m, and 925700 not valid
- Why the model refuses those: the checksum 778734, mixed case 77698, a character that is not a data character 43065, no separator 9248, a data part of fewer than 6 characters 7624, longer than 90 characters 6862, an HRP of no characters or more than 83 1391, an HRP character outside 33 to 126 1078
- Encodings asked for: 46795, of which 36375 are written and 10420 refused: an upper case letter in the HRP 4255, an HRP character outside 33 to 126 3506, longer than 90 characters 1848, an empty HRP 811
- BIP 173 and BIP 350 strings the model reads as the BIPs say: 82 of 82
- Single substitutions in the data part of a valid string that still decode: 0 of 656611
- Valid strings ending in p that stay valid with q inserted before the p: bech32: 1337 of 1337 that fit in 90 characters, 0 of 1663 of 90 characters before the insertion; bech32m: 0 of 1349 that fit in 90 characters, 0 of 1651 of 90 characters before the insertion
- Agreement with each oracle over all inputs: sipa Python 1002576 of 1012996, sipa C 1012035 of 1012996, npm 1008135 of 1012996, Go 1002576 of 1012996, Rust 1007285 of 1012996
- Malformed requests answered `error`: 35 of 35
- Requests ending in CR LF: every seventh, 144713
- Last lines sent alone, with no LF or with CR LF, answered right: 3 of 3
- Failures: 0

## Where the oracles differ

Each disagreement is counted under the reason the model confirms, with the first input that showed it.

### sipa Python

- sipa Python writes an upper case HRP as it is, with its checksum, encoding: 3879; for example `encode bech32 'A' data ''`
- sipa Python writes HRP characters outside 33 to 126, encoding: 3247; for example `encode bech32 ' ' data ''`
- sipa Python has no 90-character limit, encoding: 1848; for example `encode bech32 'a' data 'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'`
- sipa Python writes an empty HRP, encoding: 783; for example `encode bech32 '' data ''`
- sipa Python has no 90-character limit; writes an upper case HRP as it is, with its checksum, encoding: 376; for example `encode bech32 'XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX' data 'q'`
- sipa Python has no 90-character limit; writes HRP characters outside 33 to 126, encoding: 259; for example `encode bech32 '\u212a' data 'nnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn'`
- sipa Python writes an empty HRP; has no 90-character limit, encoding: 28; for example `encode bech32 '' data '555555555555555555555555555555555555555555555555555555555555555555555555555555555555'`

### sipa C

- sipa C writes an empty HRP, encoding: 783; for example `encode bech32 '' data ''`
- sipa C reads the HRP as a C string, which ends at the first NUL, encoding: 164; for example `encode bech32 '\x00' data ''`
- sipa C reads a C string, which ends at the first NUL, decoding: 14; for example `decode 'ab1qpzfg27ph\x00'`

### npm

- npm lower-cases the HRP, encoding: 3879; for example `encode bech32 'A' data ''`
- npm writes an empty HRP, encoding: 783; for example `encode bech32 '' data ''`
- npm lower-cases the HRP with Unicode rules, which turn the Kelvin sign into k, encoding: 180; for example `encode bech32 '\u212a' data ''`
- npm lower-cases with Unicode rules, so the Kelvin sign U+212A reads as k, decoding: 19; for example `decode '\u212a1\u212a\u212aS7FG6D'`

### Go

- Go lower-cases the HRP, encoding: 3879; for example `encode bech32 'A' data ''`
- Go writes HRP characters outside 33 to 126, lower-cased with Unicode rules, with the checksum over their UTF-8 bytes, encoding: 3247; for example `encode bech32 ' ' data ''`
- Go has no 90-character limit, encoding: 1848; for example `encode bech32 'a' data 'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'`
- Go writes an empty HRP, encoding: 783; for example `encode bech32 '' data ''`
- Go has no 90-character limit; lower-cases the HRP, encoding: 376; for example `encode bech32 'XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX' data 'q'`
- Go has no 90-character limit; writes HRP characters outside 33 to 126, lower-cased with Unicode rules, with the checksum over their UTF-8 bytes, encoding: 259; for example `encode bech32 '\u212a' data 'nnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn'`
- Go writes an empty HRP; has no 90-character limit, encoding: 28; for example `encode bech32 '' data '555555555555555555555555555555555555555555555555555555555555555555555555555555555555'`

### Rust

- Rust lower-cases the HRP, encoding: 2985; for example `encode bech32 'A' data ''`
- Rust has no 90-character limit (its limit is the code length, 1023), decoding: 1770; for example `decode 'a1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqql0ccdy'`
- Rust has no 90-character limit, encoding: 675; for example `encode bech32 'a' data 'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'`
- Rust has no 90-character limit; lower-cases the HRP, encoding: 281; for example `encode bech32 'XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX' data 'q'`
