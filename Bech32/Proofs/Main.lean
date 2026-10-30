/-
  The proofs of the statements in `Bech32/Spec.lean`, under the same names.
  Each statement is copied from `Bech32/Spec.lean` word for word; `lake
  comparator` checks that they match. The work is in `Bech32/Proofs/`; the
  test vectors are checked by the kernel with `decide`.
-/

import Bech32
import Bech32.Spec.Defs
import Bech32.Proofs.Checksum
import Bech32.Proofs.Decode
import Bech32.Proofs.Final

open Bech32 (Variant)

/-! ## Decoding -/

/-- `decode` reads a string exactly as BIP 173 and BIP 350 set out:
    it gives the variant, the human-readable part in lower case, and
    the data without the checksum when the string is valid, as
    `Bech32.Spec.Decodes` states it, and fails when it is not. Since `decode`
    is a function, a string has at most one reading. -/
theorem Bech32.Spec.decode_iff (s : String) (v : Variant) (hrp : String) (data : List (Fin 32)) :
    Bech32.decode s = some (v, hrp, data) ↔
      Bech32.Spec.Decodes s.toList v hrp.toList (data.map Fin.val) := 
  Bech32.Proofs.decode_iff' s v hrp data

/-! ## Encoding -/

/-- `encode` succeeds exactly when the human-readable part has at least
    one character, each in the range 33 to 126 and none an upper case
    letter, and the string fits in 90 characters: the human-readable
    part, the separator, the data and six checksum characters. -/
theorem Bech32.Spec.encode_isSome (v : Variant) (hrp : String) (data : List (Fin 32)) :
    (Bech32.encode v hrp data).isSome ↔
      hrp.toList ≠ [] ∧
      (∀ c ∈ hrp.toList, 33 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ ¬ Bech32.Spec.Upper c) ∧
      hrp.length + 1 + data.length + 6 ≤ 90 := 
  Bech32.Proofs.encode_isSome' v hrp data

/-- Decoding an encoding gives back the variant, the human-readable
    part and the data. -/
theorem Bech32.Spec.decode_encode (v : Variant) (hrp : String) (data : List (Fin 32)) (s : String)
    (h : Bech32.encode v hrp data = some s) :
    Bech32.decode s = some (v, hrp, data) := 
  Bech32.Proofs.decode_encode' v hrp data s h

/-- What `decode` accepts, `encode` writes back in lower case. So the
    valid strings are exactly the encodings and their upper case forms. -/
theorem Bech32.Spec.encode_decode (s : String) (v : Variant) (hrp : String) (data : List (Fin 32))
    (h : Bech32.decode s = some (v, hrp, data)) :
    (Bech32.encode v hrp data).map String.toList = some (s.toList.map Bech32.Spec.lower) := 
  Bech32.Proofs.encode_decode' s v hrp data h

/-- An encoding has no upper case letter. BIP 173: "Encoders MUST
    always output an all lowercase Bech32 string." -/
theorem Bech32.Spec.encode_lower (v : Variant) (hrp : String) (data : List (Fin 32)) (s : String)
    (h : Bech32.encode v hrp data = some s) :
    ∀ c ∈ s.toList, ¬ Bech32.Spec.Upper c := 
  Bech32.Proofs.encode_lower' v hrp data s h

/-! ## Errors the checksum catches -/

/-- A data character changed to another data character is always
    caught, whichever variant either string has. Take two strings that,
    in lower case, are the same but for one character after the
    separator, where they hold two different data characters. At most
    one of them decodes. A data character changed to `1` is not covered:
    see `Bech32.Spec.separator_substitution`. -/
theorem Bech32.Spec.one_substitution (s s' : String) (p q : List Char) (x y : Char)
    (hp : '1' ∈ p) (hq : '1' ∉ q)
    (hx : x ∈ Bech32.Spec.charset) (hy : y ∈ Bech32.Spec.charset) (hxy : x ≠ y)
    (hs : s.toList.map Bech32.Spec.lower = p ++ x :: q)
    (hs' : s'.toList.map Bech32.Spec.lower = p ++ y :: q) :
    Bech32.decode s = none ∨ Bech32.decode s' = none := 
  Bech32.Proofs.one_substitution' s s' p q x y hp hq hx hy hxy hs hs'

/-- What `Bech32.Spec.one_substitution` leaves out. A data character changed
    to `1` moves the separator, since the separator is the last `1`, and
    both strings can then be valid: under one variant, as in the first
    pair, or under both, as in the second. -/
theorem Bech32.Spec.separator_substitution :
    (Bech32.decode "bc1et06sdxfhesf7").map (·.1) = some .bech32 ∧
    Bech32.decode "bc1et06sd1fhesf7" = some (.bech32, "bc1et06sd", []) ∧
    (Bech32.decode "bc1xd49x4cqqzp2cp6").map (·.1) = some .bech32 ∧
    Bech32.decode "bc1xd49x41qqzp2cp6" = some (.bech32m, "bc1xd49x4", [0, 0]) := by
  and_intros <;> decide +kernel

/-- The weakness that BIP 350 fixes: inserting `q` before a final `p`
    keeps a Bech32 string valid, as long as it still fits in 90
    characters. -/
theorem Bech32.Spec.insert_q_bech32 (s : String) (hrp : String) (data : List (Fin 32)) (p : List Char)
    (h : Bech32.decode s = some (.bech32, hrp, data))
    (hp : s.toList.map Bech32.Spec.lower = p ++ ['p']) (hlen : s.length < 90) :
    ∃ data', Bech32.decode (String.ofList (p ++ ['q', 'p'])) = some (.bech32, hrp, data') := 
  Bech32.Proofs.insert_q_bech32' s hrp data p h hp hlen

/-- Bech32m does not have that weakness: inserting `q` before a final
    `p` of a Bech32m string never gives a valid string, of either
    variant. -/
theorem Bech32.Spec.insert_q_bech32m (s : String) (hrp : String) (data : List (Fin 32)) (p : List Char)
    (h : Bech32.decode s = some (.bech32m, hrp, data))
    (hp : s.toList.map Bech32.Spec.lower = p ++ ['p']) :
    Bech32.decode (String.ofList (p ++ ['q', 'p'])) = none := 
  Bech32.Proofs.insert_q_bech32m' s hrp data p h hp

/-! ## Test vectors -/

/-- The valid Bech32 strings of BIP 173. -/
theorem Bech32.Spec.bip173_valid :
    Bech32.decode "A12UEL5L" = some (.bech32, "a", []) ∧
    Bech32.decode "a12uel5l" = some (.bech32, "a", []) ∧
    Bech32.decode "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1tt5tgs" =
      some (.bech32, "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio", []) ∧
    Bech32.decode "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw" =
      some (.bech32, "abcdef", List.finRange 32) ∧
    Bech32.decode "11qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqc8247j" =
      some (.bech32, "1", List.replicate 82 0) ∧
    (Bech32.decode "split1checkupstagehandshakeupstreamerranterredcaperred2y9e3w").map (·.1) =
      some .bech32 ∧
    Bech32.decode "?1ezyfcl" = some (.bech32, "?", []) := by
  and_intros <;> decide +kernel

/-- The invalid strings of BIP 173, with the reasons it gives. -/
theorem Bech32.Spec.bip173_invalid :
    -- HRP character out of range
    Bech32.decode "\x201nwldj5" = none ∧
    Bech32.decode "\x7F1axkwrx" = none ∧
    Bech32.decode "\x801eym55h" = none ∧
    -- overall max length exceeded
    Bech32.decode "an84characterslonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1569pvx" = none ∧
    -- no separator character
    Bech32.decode "pzry9x0s0muk" = none ∧
    -- empty HRP
    Bech32.decode "1pzry9x0s0muk" = none ∧
    -- invalid data character
    Bech32.decode "x1b4n0q5v" = none ∧
    -- too short checksum
    Bech32.decode "li1dgmt3" = none ∧
    -- invalid character in checksum
    Bech32.decode "de1lg7wt\xFF" = none ∧
    -- checksum calculated with uppercase form of HRP
    Bech32.decode "A1G7SGD8" = none ∧
    -- empty HRP
    Bech32.decode "10a06t8" = none ∧
    Bech32.decode "1qzzfhee" = none := by
  and_intros <;> decide +kernel

/-- The valid Bech32m strings of BIP 350. "No string can be
    simultaneously valid Bech32 and Bech32m, so the above examples also
    serve as invalid test vectors for Bech32": each reads as Bech32m. -/
theorem Bech32.Spec.bip350_valid :
    Bech32.decode "A1LQFN3A" = some (.bech32m, "a", []) ∧
    Bech32.decode "a1lqfn3a" = some (.bech32m, "a", []) ∧
    Bech32.decode "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11sg7hg6" =
      some (.bech32m, "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber1", []) ∧
    Bech32.decode "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx" =
      some (.bech32m, "abcdef", (List.finRange 32).reverse) ∧
    Bech32.decode "11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllludsr8" =
      some (.bech32m, "1", List.replicate 82 31) ∧
    (Bech32.decode "split1checkupstagehandshakeupstreamerranterredcaperredlc445v").map (·.1) =
      some .bech32m ∧
    Bech32.decode "?1v759aa" = some (.bech32m, "?", []) := by
  and_intros <;> decide +kernel

/-- The invalid Bech32m strings of BIP 350, with the reasons it gives. -/
theorem Bech32.Spec.bip350_invalid :
    -- HRP character out of range
    Bech32.decode "\x201xj0phk" = none ∧
    Bech32.decode "\x7F1g6xzxy" = none ∧
    Bech32.decode "\x801vctc34" = none ∧
    -- overall max length exceeded
    Bech32.decode "an84characterslonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11d6pts4" = none ∧
    -- no separator character
    Bech32.decode "qyrz8wqd2c9m" = none ∧
    -- empty HRP
    Bech32.decode "1qyrz8wqd2c9m" = none ∧
    -- invalid data character
    Bech32.decode "y1b0jsk6g" = none ∧
    Bech32.decode "lt1igcx5c0" = none ∧
    -- too short checksum
    Bech32.decode "in1muywd" = none ∧
    -- invalid character in checksum
    Bech32.decode "mm1crxm3i" = none ∧
    Bech32.decode "au1s5cgom" = none ∧
    -- checksum calculated with uppercase form of HRP
    Bech32.decode "M1VUXWEZ" = none ∧
    -- empty HRP
    Bech32.decode "16plkw9" = none ∧
    Bech32.decode "1p2gdwpf" = none := by
  and_intros <;> decide +kernel

/-- The segwit address vectors of BIP 173 and BIP 350, read as strings.
    This slice checks the string layer only: most of the addresses
    those BIPs call invalid are valid strings, which a segwit decoder
    (a later slice) rejects for their witness version, program length,
    padding or variant. The comment on each line gives the BIP's
    verdict on the address: BIP 350's, then the eight addresses only
    BIP 173 lists. -/
theorem Bech32.Spec.segwit_strings :
    -- valid addresses
    (Bech32.decode "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4").map (·.1) = some .bech32 ∧
    (Bech32.decode "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7").map (·.1) = some .bech32 ∧
    (Bech32.decode "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y").map (·.1) = some .bech32m ∧
    Bech32.decode "BC1SW50QGDZ25J" = some (.bech32m, "bc", [16, 14, 20, 15, 0]) ∧
    (Bech32.decode "bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs").map (·.1) = some .bech32m ∧
    (Bech32.decode "tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy").map (·.1) = some .bech32 ∧
    (Bech32.decode "tb1pqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesf3hn0c").map (·.1) = some .bech32m ∧
    (Bech32.decode "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0").map (·.1) = some .bech32m ∧
    -- valid under BIP 173 only: v1 and later now need Bech32m
    (Bech32.decode "bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7k7grplx").map (·.1) = some .bech32 ∧
    Bech32.decode "BC1SW50QA3JX3S" = some (.bech32, "bc", [16, 14, 20, 15, 0]) ∧
    (Bech32.decode "bc1zw508d6qejxtdg4y5r3zarvaryvg6kdaj").map (·.1) = some .bech32 ∧
    -- invalid human-readable part
    (Bech32.decode "tc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq5zuyut").map (·.1) = some .bech32m ∧
    -- Bech32 instead of Bech32m
    (Bech32.decode "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqh2y7hd").map (·.1) = some .bech32 ∧
    (Bech32.decode "tb1z0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqglt7rf").map (·.1) = some .bech32 ∧
    (Bech32.decode "BC1S0XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ54WELL").map (·.1) = some .bech32 ∧
    -- Bech32m instead of Bech32
    (Bech32.decode "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kemeawh").map (·.1) = some .bech32m ∧
    (Bech32.decode "tb1q0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq24jc47").map (·.1) = some .bech32m ∧
    -- invalid character in checksum
    Bech32.decode "bc1p38j9r5y49hruaue7wxjce0updqjuyyx0kh56v8s25huc6995vvpql3jow4" = none ∧
    -- invalid witness version
    (Bech32.decode "BC130XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ7ZWS8R").map (·.1) = some .bech32m ∧
    -- invalid program length
    (Bech32.decode "bc1pw5dgrnzv").map (·.1) = some .bech32m ∧
    (Bech32.decode "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v8n0nx0muaewav253zgeav").map (·.1) = some .bech32m ∧
    (Bech32.decode "BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P").map (·.1) = some .bech32 ∧
    -- mixed case
    Bech32.decode "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq47Zagq" = none ∧
    -- zero padding of more than 4 bits
    (Bech32.decode "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v07qwwzcrf").map (·.1) = some .bech32m ∧
    -- non-zero padding in 8-to-5 conversion
    (Bech32.decode "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vpggkg4j").map (·.1) = some .bech32m ∧
    -- empty data section
    Bech32.decode "bc1gmk9yu" = some (.bech32, "bc", []) ∧
    -- BIP 173 only: invalid human-readable part
    (Bech32.decode "tc1qw508d6qejxtdg4y5r3zarvary0c5xw7kg3g4ty").map (·.1) = some .bech32 ∧
    -- BIP 173 only: invalid checksum
    Bech32.decode "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t5" = none ∧
    -- BIP 173 only: invalid witness version
    (Bech32.decode "BC13W508D6QEJXTDG4Y5R3ZARVARY0C5XW7KN40WF2").map (·.1) = some .bech32 ∧
    -- BIP 173 only: invalid program length
    (Bech32.decode "bc1rw5uspcuh").map (·.1) = some .bech32 ∧
    (Bech32.decode "bc10w508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kw5rljs90").map (·.1) = some .bech32 ∧
    -- BIP 173 only: mixed case
    Bech32.decode "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sL5k7" = none ∧
    -- BIP 173 only: zero padding of more than 4 bits
    (Bech32.decode "bc1zw508d6qejxtdg4y5r3zarvaryvqyzf3du").map (·.1) = some .bech32 ∧
    -- BIP 173 only: non-zero padding in 8-to-5 conversion
    (Bech32.decode "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3pjxtptv").map (·.1) = some .bech32 := by
  and_intros <;> decide +kernel

/-- Encodings: the BIP strings that are encodings, and the limits of
    `encode`. -/
theorem Bech32.Spec.encode_vectors :
    Bech32.encode .bech32 "a" [] = some "a12uel5l" ∧
    Bech32.encode .bech32m "a" [] = some "a1lqfn3a" ∧
    Bech32.encode .bech32 "abcdef" (List.finRange 32) =
      some "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw" ∧
    Bech32.encode .bech32m "abcdef" (List.finRange 32).reverse =
      some "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx" ∧
    Bech32.encode .bech32 "?" [] = some "?1ezyfcl" ∧
    -- an empty human-readable part
    Bech32.encode .bech32 "" [] = none ∧
    -- an upper case letter, a space, and DEL in the human-readable part
    Bech32.encode .bech32 "A" [] = none ∧
    Bech32.encode .bech32 " " [] = none ∧
    Bech32.encode .bech32 "\x7F" [] = none ∧
    -- 90 characters fit, 91 do not
    (Bech32.encode .bech32 "a" (List.replicate 82 0)).isSome ∧
    Bech32.encode .bech32 "a" (List.replicate 83 0) = none := by
  and_intros <;> decide +kernel
