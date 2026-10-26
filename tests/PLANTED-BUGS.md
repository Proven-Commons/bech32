# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a one-line change to `Bech32/Basic.lean`, tested with `tests/run_tests.py --count 1000`. Every bug must give failures, and the unchanged code none. A bug that does not build counts as missed.

| Planted bug | Failures |
|---|---|
| none | 0 |
| one generator constant is wrong | 26823 |
| the checksum keeps 26 bits before the shift, not 25 | 6798 |
| a string of 91 characters is allowed | 496 |
| the HRP may be empty | 132 |
| mixed case is allowed | 6108 |
| the first 1 is taken as the separator | 1891 |
| the Bech32m constant has two digits swapped | 13224 |
| the HRP expansion leaves out the zero | 26823 |
| the HRP is checksummed in upper case | 11312 |
| two characters of the charset are swapped | 15146 |

Bugs caught: 10 of 10
