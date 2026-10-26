# Where these files come from

`segwit_addr.py`, `segwit_addr.c` and `segwit_addr.h` are the reference
implementations of Bech32 and Bech32m by Pieter Wuille, the author of
BIP 173 and BIP 350, from https://github.com/sipa/bech32 at commit
`7a7d7ab158db7078a333384e0e918c90dbc42917`. They are copied byte for
byte, with nothing changed:

| File here | Path in sipa/bech32 | SHA-256 |
|---|---|---|
| `segwit_addr.py` | `ref/python/segwit_addr.py` | `2884ce04a36c8374c4249177cd90e91e545ac73b5c9260307bbeb74ae2e9de0f` |
| `segwit_addr.c` | `ref/c/segwit_addr.c` | `aa73529c41142d2a9fed384676910943692236eda2ec583f96a95b5283c3042d` |
| `segwit_addr.h` | `ref/c/segwit_addr.h` | `1b70ce1aad01cd8e99ed1814e191d80a1c47feda65afb652eebef3be35620733` |

Each was fetched from
`https://raw.githubusercontent.com/sipa/bech32/7a7d7ab158db7078a333384e0e918c90dbc42917/<path>`.
`tests/run_tests.py` checks the three hashes before it uses the files,
and leaves the oracle out, with a failure, if one differs.

Each file carries its MIT licence in its header comment.

`wrapper.c` is new: it drives `bech32_encode` and `bech32_decode`
through standard input and output for `tests/run_tests.py`.
