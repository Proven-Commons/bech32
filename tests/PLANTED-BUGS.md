# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a one-line change to `Bech32/Basic.lean`, tested with `tests/run_tests.py --count 1000 --no-oracles`, so each failure is the tool disagreeing with the model or a BIP vector. Every bug must give failures, and the unchanged code none. A bug that does not build, or a run that gives up, counts as missed.

| Planted bug | Failures |
|---|---|
| none | 0 |
| one generator constant is wrong | 4484 |
| the checksum keeps 26 bits before the shift, not 25 | 1151 |
| a string of 91 characters is allowed | 104 |
| the HRP may be empty | 22 |
| mixed case is allowed | 1019 |
| the first 1 is taken as the separator | 341 |
| the Bech32m constant has two digits swapped | 2163 |
| the HRP expansion leaves out the zero | 4478 |
| the HRP is checksummed in upper case | 1865 |
| two characters of the charset are swapped | 2579 |
| o is read as the digit 0 | 14 |
| a data part of 5 characters is allowed | 19 |
| the encoder writes 91 characters | 17 |
| the encoder writes an upper case HRP | 475 |
| the encoder writes an empty HRP | 40 |

Bugs caught: 15 of 15
