# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a one-line change to `Bech32/Basic.lean`, tested with `tests/run_tests.py --count 1000`. Every bug must give failures, and the unchanged code none. A bug that does not build counts as missed.

| Planted bug | Failures |
|---|---|
| none | 0 |
| one generator constant is wrong | 26884 |
| the checksum keeps 26 bits before the shift, not 25 | 6906 |
| a string of 91 characters is allowed | 526 |
| the HRP may be empty | 132 |
| mixed case is allowed | 6114 |
| the first 1 is taken as the separator | 2041 |
| the Bech32m constant has two digits swapped | 12978 |
| the HRP expansion leaves out the zero | 26853 |
| the HRP is checksummed in upper case | 11180 |
| two characters of the charset are swapped | 15464 |
| o is read as the digit 0 | 84 |
| a data part of 5 characters is allowed | 114 |

Bugs caught: 12 of 12
