/-
  The definitions the statements in `Spec.lean` use, written from
  BIP 173 (https://github.com/bitcoin/bips/blob/master/bip-0173.mediawiki)
  and BIP 350 (https://github.com/bitcoin/bips/blob/master/bip-0350.mediawiki).

  This file is part of the specification: a reviewer approves it with
  `Spec.lean`. It shares nothing with the code in `Bech32/` but the
  type `Bech32.Variant`, which names the two variants.

  BIP 173 makes its Python code for the checksum normative ("Valid
  strings MUST pass the criteria for validity specified by the Python3
  code snippet below"), so `polymod` and `hrpExpand` copy that code
  line for line.
-/

import Bech32

namespace Spec

open Bech32 (Variant)

/-- The data characters of BIP 173, in the order of their values: the
    table there, row by row. `q` is 0, `p` is 1, and `l` is 31. -/
def charset : List Char :=
  ['q', 'p', 'z', 'r', 'y', '9', 'x', '8',
   'g', 'f', '2', 't', 'v', 'd', 'w', '0',
   's', '3', 'j', 'n', '5', '4', 'k', 'h',
   'c', 'e', '6', 'm', 'u', 'a', '7', 'l']

/-- The data character for a value. Only values below 32 are used. -/
def dataChar (v : Nat) : Char := charset.getD v 'q'

/-- `GEN` in `bech32_polymod`. -/
def GEN : List Nat := [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]

/-- `bech32_polymod` of BIP 173:

    ```
    def bech32_polymod(values):
      GEN = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
      chk = 1
      for v in values:
        b = (chk >> 25)
        chk = (chk & 0x1ffffff) << 5 ^ v
        for i in range(5):
          chk ^= GEN[i] if ((b >> i) & 1) else 0
      return chk
    ```
    In Python, `<<` binds more tightly than `^`, as it does in Lean. -/
def polymod (values : List Nat) : Nat :=
  values.foldl
    (fun chk v =>
      let b := chk >>> 25
      let chk := ((chk &&& 0x1ffffff) <<< 5) ^^^ v
      (List.range 5).foldl
        (fun chk i => chk ^^^ (if (b >>> i) &&& 1 = 1 then GEN.getD i 0 else 0)) chk)
    1

/-- `bech32_hrp_expand` of BIP 173:

    ```
    def bech32_hrp_expand(s):
      return [ord(x) >> 5 for x in s] + [0] + [ord(x) & 31 for x in s]
    ``` -/
def hrpExpand (s : List Char) : List Nat :=
  s.map (fun x => x.toNat >>> 5) ++ [0] ++ s.map (fun x => x.toNat &&& 31)

/-- The constant the checksum must give: 1 for Bech32 (BIP 173),
    `0x2bc830a3` for Bech32m (`BECH32M_CONST` of BIP 350). -/
def const : Variant → Nat
  | .bech32 => 1
  | .bech32m => 0x2bc830a3

/-- An upper case ASCII letter. -/
def Upper (c : Char) : Prop := 'A' ≤ c ∧ c ≤ 'Z'

/-- A lower case ASCII letter. -/
def Lower (c : Char) : Prop := 'a' ≤ c ∧ c ≤ 'z'

/-- The lower case form of a character: an upper case ASCII letter
    becomes the letter 32 code points above it, and anything else
    stays. BIP 173: "The lowercase form is used when determining a
    character's value for checksum purposes." -/
def lower (c : Char) : Char :=
  if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- `s` is a valid string of variant `v` by BIP 173 and BIP 350. Its
    human-readable part, in lower case, is `hrp`, and its data part,
    checksum included, has the values `values`. -/
structure Valid (s : List Char) (v : Variant) (hrp : List Char) (values : List Nat) : Prop where
  /-- "A Bech32 string is at most 90 characters long." -/
  length : s.length ≤ 90
  /-- Every character is US-ASCII in the range 33 to 126. BIP 173 says
      this of the human-readable part; the separator and the data
      characters are in that range too. -/
  range : ∀ c ∈ s, 33 ≤ c.toNat ∧ c.toNat ≤ 126
  /-- "Decoders MUST NOT accept strings where some characters are
      uppercase and some are lowercase." -/
  not_mixed : ¬ ((∃ c ∈ s, Upper c) ∧ (∃ c ∈ s, Lower c))
  /-- In lower case, the string is the human-readable part, the
      separator `1`, and the data characters. No data character is
      `1`, so the separator is the last `1` in the string. -/
  parts : s.map lower = hrp ++ ['1'] ++ values.map dataChar
  /-- Each value is that of a data character. -/
  values_lt : ∀ x ∈ values, x < 32
  /-- "This part MUST contain 1 to 83 US-ASCII characters." -/
  hrp_length : 1 ≤ hrp.length ∧ hrp.length ≤ 83
  /-- "The data part, which is at least 6 characters long." -/
  data_length : 6 ≤ values.length
  /-- The checksum: `bech32_verify_checksum` of BIP 173 for Bech32,
      `bech32m_verify_checksum` of BIP 350 for Bech32m. -/
  checksum : polymod (hrpExpand hrp ++ values) = const v

/-- `s` reads as variant `v`, human-readable part `hrp` and data
    `data`: it is valid with the values of `data` followed by six
    checksum values. -/
def Decodes (s : List Char) (v : Variant) (hrp : List Char) (data : List Nat) : Prop :=
  ∃ check : List Nat, check.length = 6 ∧ Valid s v hrp (data ++ check)

end Spec
