/-
  Bech32 and Bech32m strings: BIP 173 and BIP 350.

  A string is a human-readable part (HRP), the separator `1`, and a
  data part of characters from a 32-character set, the last six of
  which are a checksum. The two variants differ only in the constant
  the checksum must give: 1 for Bech32, `0x2bc830a3` for Bech32m.

  `encode` writes a string, and `decode` reads one back. The statements
  about them are in `Bech32/Spec.lean`. The type of the two variants is in
  `Bech32/Variant.lean`, which is part of the specification.
-/

import Bech32.Variant

namespace Bech32

/-- The constant the checksum of each variant gives. -/
def Variant.const : Variant → Nat
  | .bech32 => 1
  | .bech32m => 0x2bc830a3

/-- The data characters, in the order of their values. -/
def charset : List Char := "qpzry9x8gf2tvdw0s3jn54khce6mua7l".toList

/-- The character for a value below 32. -/
def charOf (v : Fin 32) : Char := charset.getD v.val 'q'

/-- The value of a lower case data character. -/
def valueOf (c : Char) : Option (Fin 32) :=
  let i := charset.idxOf c
  if h : i < 32 then some ⟨i, h⟩ else none

/-- One step of the checksum: the loop body of `bech32_polymod` in
    BIP 173. -/
def polymodStep (chk v : Nat) : Nat :=
  let b := chk >>> 25
  let chk := ((chk &&& 0x1ffffff) <<< 5) ^^^ v
  let chk := if b &&& 1 = 0 then chk else chk ^^^ 0x3b6a57b2
  let chk := if b &&& 2 = 0 then chk else chk ^^^ 0x26508e6d
  let chk := if b &&& 4 = 0 then chk else chk ^^^ 0x1ea119fa
  let chk := if b &&& 8 = 0 then chk else chk ^^^ 0x3d4233dd
  if b &&& 16 = 0 then chk else chk ^^^ 0x2a1462b3

/-- The checksum of a list of values, starting from 1. -/
def polymod (vs : List Nat) : Nat := vs.foldl polymodStep 1

/-- The values the HRP feeds into the checksum: the high bits of each
    character, a zero, then the low bits of each character. -/
def hrpExpand (hrp : List Char) : List Nat :=
  hrp.map (fun c => c.toNat >>> 5) ++ [0] ++ hrp.map (fun c => c.toNat &&& 31)

/-- A character the HRP may hold: US-ASCII 33 to 126. -/
def isPrintable (c : Char) : Bool := 33 ≤ c.toNat && c.toNat ≤ 126

def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

def isLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

/-- Lower case for ASCII letters; other characters stay. -/
def toLower (c : Char) : Char := if isUpper c then Char.ofNat (c.toNat + 32) else c

/-- The six checksum values for `values` under variant `v`
    (`bech32_create_checksum`). -/
def checksum (v : Variant) (hrp : List Char) (values : List Nat) : List (Fin 32) :=
  let pm := polymod (hrpExpand hrp ++ values ++ [0, 0, 0, 0, 0, 0]) ^^^ v.const
  [25, 20, 15, 10, 5, 0].map fun k => Fin.ofNat 32 (pm >>> k)

/-- The checksum variant that `values` satisfy, if any. -/
def variantOf (hrp : List Char) (values : List Nat) : Option Variant :=
  let pm := polymod (hrpExpand hrp ++ values)
  if pm = Variant.bech32.const then some .bech32
  else if pm = Variant.bech32m.const then some .bech32m
  else none

/-- Split at the last `1`. -/
def splitLast (cs : List Char) : Option (List Char × List Char) :=
  match cs.reverse.idxOf? '1' with
  | none => none
  | some i => some (cs.take (cs.length - 1 - i), cs.drop (cs.length - i))

/-- Write the string for HRP `hrp` and data `data` under variant `v`.
    It fails when the HRP is empty, has a character outside 33 to 126
    or an upper case letter, or when the string would be longer than
    90 characters. -/
def encode (v : Variant) (hrp : String) (data : List (Fin 32)) : Option String :=
  let h := hrp.toList
  if h.isEmpty || !h.all (fun c => isPrintable c && !isUpper c) || 90 < h.length + 7 + data.length then
    none
  else
    some (String.ofList (h ++ '1' :: (data ++ checksum v h (data.map (·.val))).map charOf))

/-- Read a string: the variant, the HRP in lower case, and the data
    without the checksum. It fails unless the string has at most 90
    characters, all from 33 to 126, not mixed case, with an HRP of at
    least one character, a data part of at least six data characters,
    and a checksum that gives one of the two constants. -/
def decode (s : String) : Option (Variant × String × List (Fin 32)) :=
  let cs := s.toList
  if 90 < cs.length || !cs.all isPrintable || (cs.any isUpper && cs.any isLower) then none
  else
    match splitLast (cs.map toLower) with
    | none => none
    | some (hrp, rest) =>
      if hrp.isEmpty || rest.length < 6 then none
      else
        match rest.mapM valueOf with
        | none => none
        | some data =>
          match variantOf hrp (data.map (·.val)) with
          | none => none
          | some v => some (v, String.ofList hrp, data.take (data.length - 6))

end Bech32
