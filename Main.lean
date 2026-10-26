/-
  Command line front end.

    bech32 decode STRING
    bech32 encode bech32|bech32m HRP VALUES

  print the variant, the human-readable part and the data values of a
  string, or the string for a human-readable part and values (decimal,
  separated by commas, or empty). They exit with 1 when the string is
  not valid or cannot be written.

    bech32 serve

  answers requests on standard input, one per line, for the
  differential tests. A string is sent as the hex digits of its UTF-8
  bytes, and a list of values as two hex digits per value. An empty
  field is written `-`.

    decode HEX                  prints  OK, the variant, the hex of the
                                        human-readable part and the
                                        values, or FAIL
    encode VARIANT HEX VALUES   prints  OK and the hex of the string,
                                        or FAIL

  A malformed request prints `error`: an unknown operation or variant,
  the wrong number of fields, hex digits that are not in pairs, bytes
  that are not UTF-8, or a value of 32 or more. A request line may end
  in LF or CR LF.

  Every answer comes from the proved functions in `Bech32/`: `encode`
  and `decode`. The hex coding and the request handling here are
  covered by the tests, not by a proof.
-/

import Bech32

open Bech32

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexValue a
    let lo ← hexValue b
    let bs ← hexBytes rest
    pure ((hi * 16 + lo).toUInt8 :: bs)
  | [_] => none

/-- The bytes a field gives: `-` for none, else hex digits in pairs. -/
def fieldBytes (f : String) : Option (List UInt8) :=
  if f = "-" then some [] else if f.isEmpty then none else hexBytes f.toList

/-- The string whose UTF-8 bytes the field gives. -/
def fromHex (f : String) : Option String := do
  let bs ← fieldBytes f
  String.fromUTF8? ⟨bs.toArray⟩

/-- The values the field gives, each below 32. -/
def fromHexValues (f : String) : Option (List (Fin 32)) := do
  let bs ← fieldBytes f
  bs.mapM fun b => if h : b.toNat < 32 then some ⟨b.toNat, h⟩ else none

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

def hexByte (n : Nat) : List Char := [hexDigit (n / 16), hexDigit (n % 16)]

/-- A field for a list of bytes: `-` when it is empty. -/
def toField (bs : List Nat) : String :=
  if bs.isEmpty then "-" else String.ofList (bs.flatMap hexByte)

def variantName : Variant → String
  | .bech32 => "bech32"
  | .bech32m => "bech32m"

def variantOfName : String → Option Variant
  | "bech32" => some .bech32
  | "bech32m" => some .bech32m
  | _ => none

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["decode", h] => do
    let s ← fromHex h
    pure (match decode s with
      | some (v, hrp, data) =>
        s!"OK {variantName v} {toField (hrp.toUTF8.toList.map (·.toNat))} {toField (data.map (·.val))}"
      | none => "FAIL")
  | ["encode", vn, h, vs] => do
    let v ← variantOfName vn
    let hrp ← fromHex h
    let data ← fromHexValues vs
    pure (match encode v hrp data with
      | some s => "OK " ++ toField (s.toUTF8.toList.map (·.toNat))
      | none => "FAIL")
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn ((request (chomp line)).getD "error")

/-- Values written in decimal, separated by commas. -/
def parseValues (s : String) : Option (List (Fin 32)) :=
  if s.isEmpty then some []
  else (s.splitOn ",").mapM fun t => do
    let n ← t.toNat?
    if h : n < 32 then some ⟨n, h⟩ else none

def usage : String :=
  "usage: bech32 decode STRING\n       bech32 encode bech32|bech32m HRP VALUES\n       bech32 serve"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["decode", s] =>
    match decode s with
    | some (v, hrp, data) =>
      IO.println s!"{variantName v} {hrp} {",".intercalate (data.map (toString ·.val))}"
      return 0
    | none => IO.eprintln "not a valid Bech32 or Bech32m string"; return 1
  | ["encode", vn, hrp, vs] =>
    match variantOfName vn, parseValues vs with
    | some v, some data =>
      match encode v hrp data with
      | some s => IO.println s; return 0
      | none => IO.eprintln "cannot encode: check the human-readable part and the length"; return 1
    | _, _ => IO.eprintln usage; return 2
  | ["serve"] => serve; return 0
  | _ => IO.eprintln usage; return 2
