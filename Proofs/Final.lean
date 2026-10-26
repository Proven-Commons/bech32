/-
  The remaining statements of `Spec.lean`: decoding an encoding,
  encoding what was decoded, one changed data character, and inserting
  `q` before a final `p`.

  They combine `decode_iff'` and the facts about characters in
  `Proofs/Decode.lean` with the checksum algebra of
  `Proofs/Checksum.lean`.
-/

import Proofs.Checksum
import Proofs.Decode

namespace Bech32.Proofs

/-! ## Helpers -/

/-- The values of an HRP of characters up to 126 are below 32. -/
theorem fin_hrpExpand_lt (hrp : List Char) (h : ∀ c ∈ hrp, c.toNat ≤ 126) :
    ∀ x ∈ Bech32.hrpExpand hrp, x < 32 := by
  intro x hx
  simp only [Bech32.hrpExpand, List.mem_append, List.mem_map, List.mem_singleton] at hx
  rcases hx with (⟨c, hc, rfl⟩ | rfl) | ⟨c, hc, rfl⟩
  · have := h c hc
    rw [Nat.shiftRight_eq_div_pow]
    omega
  · decide
  · have : c.toNat &&& 31 ≤ 31 := Nat.and_le_right
    omega

/-- The characters of a lower case form are in range and not upper case. -/
theorem fin_mem_map_lower (s : List Char) (hs : ∀ c ∈ s, 33 ≤ c.toNat ∧ c.toNat ≤ 126) :
    ∀ c ∈ s.map Spec.lower, (33 ≤ c.toNat ∧ c.toNat ≤ 126) ∧ ¬ Spec.Upper c := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  exact ⟨lower_range c' (hs c' hc'), not_upper_lower c'⟩

/-- A list with no upper case letter is its own lower case form. -/
theorem fin_map_lower_of_not_upper (l : List Char) (h : ∀ c ∈ l, ¬ Spec.Upper c) :
    l.map Spec.lower = l := by
  conv => rhs; rw [← List.map_id l]
  exact List.map_congr_left fun c hc => lower_of_not_upper c (h c hc)

/-- The HRP of a valid string is in range and not upper case. -/
theorem fin_valid_hrp {s : List Char} {v : Bech32.Variant} {hrp : List Char} {vals : List Nat}
    (hv : Spec.Valid s v hrp vals) :
    ∀ c ∈ hrp, (33 ≤ c.toNat ∧ c.toNat ≤ 126) ∧ ¬ Spec.Upper c := by
  intro c hc
  apply fin_mem_map_lower s hv.range
  rw [hv.parts]
  exact List.mem_append_left _ (List.mem_append_left _ hc)

/-- The length of a valid string, by parts. -/
theorem fin_valid_length {s : List Char} {v : Bech32.Variant} {hrp : List Char}
    {vals : List Nat} (hv : Spec.Valid s v hrp vals) :
    s.length = hrp.length + 1 + vals.length := by
  have := congrArg List.length hv.parts
  simp only [List.length_map, List.length_append, List.length_singleton] at this
  omega

theorem fin_dataChar_inj (a b : Nat) (ha : a < 32) (hb : b < 32)
    (h : Spec.dataChar a = Spec.dataChar b) : a = b := by
  have e1 := valueOf_dataChar ⟨a, ha⟩
  have e2 := valueOf_dataChar ⟨b, hb⟩
  simp only at e1 e2
  rw [h, e2] at e1
  simp only [Option.some.injEq, Fin.mk.injEq] at e1
  exact e1.symm

theorem fin_map_dataChar_inj (l l' : List Nat) (h : ∀ x ∈ l, x < 32) (h' : ∀ x ∈ l', x < 32)
    (e : l.map Spec.dataChar = l'.map Spec.dataChar) : l = l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons _ _ => simp at e
  | cons a l ih =>
    cases l' with
    | nil => simp at e
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq] at e
      rw [fin_dataChar_inj a b (h a List.mem_cons_self) (h' b List.mem_cons_self) e.1,
        ih l' (fun x hx => h x (List.mem_cons_of_mem _ hx))
          (fun x hx => h' x (List.mem_cons_of_mem _ hx)) e.2]

/-- A lower case string of the right shape, with the right checksum, is valid. -/
theorem fin_valid_of_lower (t : List Char) (v : Bech32.Variant) (hrp : List Char)
    (W : List Nat) (hlen : t.length ≤ 90)
    (hrange : ∀ c ∈ hrp, (33 ≤ c.toNat ∧ c.toNat ≤ 126) ∧ ¬ Spec.Upper c)
    (ht : t = hrp ++ ['1'] ++ W.map Spec.dataChar)
    (hW : ∀ x ∈ W, x < 32) (hne : hrp ≠ []) (h6 : 6 ≤ W.length)
    (hsum : Spec.polymod (Spec.hrpExpand hrp ++ W) = Spec.const v) :
    Spec.Valid t v hrp W := by
  have hall : ∀ c ∈ t, (33 ≤ c.toNat ∧ c.toNat ≤ 126) ∧ ¬ Spec.Upper c := by
    intro c hc
    rw [ht] at hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with (hc | rfl) | hc
    · exact hrange c hc
    · unfold Spec.Upper; decide
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
      have hm := dataChar_mem x (hW x hx)
      exact ⟨charset_range _ hm, charset_not_upper _ hm⟩
  have hl := congrArg List.length ht
  simp only [List.length_append, List.length_singleton, List.length_map] at hl
  exact {
    length := hlen
    range := fun c hc => (hall c hc).1
    not_mixed := fun ⟨⟨c, hc, hu⟩, _⟩ => (hall c hc).2 hu
    parts := by rw [fin_map_lower_of_not_upper t (fun c hc => (hall c hc).2)]; exact ht
    values_lt := hW
    hrp_length := ⟨List.length_pos_iff.2 hne, by omega⟩
    data_length := h6
    checksum := hsum }

/-- A valid string decodes, to some data. -/
theorem fin_decode_of_valid (t : String) (v : Bech32.Variant) (hrp : String) (W : List Nat)
    (hv : Spec.Valid t.toList v hrp.toList W) :
    ∃ data, Bech32.decode t = some (v, hrp, data) := by
  obtain ⟨data, hdata⟩ := exists_fin_list (W.take (W.length - 6))
    (fun x hx => hv.values_lt x (List.mem_of_mem_take hx))
  refine ⟨data, (decode_iff' t v hrp data).2 ⟨W.drop (W.length - 6), ?_, ?_⟩⟩
  · have := hv.data_length
    simp only [List.length_drop]
    omega
  · rw [hdata, List.take_append_drop]
    exact hv

/-- When `encode` succeeds, what it writes. -/
theorem fin_encode_eq (v : Bech32.Variant) (hrp : String) (data : List (Fin 32))
    (hc : hrp.toList ≠ [] ∧
      (∀ c ∈ hrp.toList, 33 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ ¬ Spec.Upper c) ∧
      hrp.length + 1 + data.length + 6 ≤ 90) :
    Bech32.encode v hrp data = some (String.ofList (hrp.toList ++ '1' ::
      (data.map Fin.val ++ (Bech32.checksum v hrp.toList (data.map Fin.val)).map Fin.val).map
        Spec.dataChar)) := by
  have hc' := (encode_cond_iff hrp data).2 hc
  simp only [Bech32.encode]
  rw [ite_eq_right_of_eq_false _ _ (eq_false hc')]
  have hf : Bech32.charOf = fun x => Spec.dataChar x.val := funext charOf_eq
  rw [hf]
  simp only [Option.some.injEq, List.map_append, List.map_map]
  rfl

theorem fin_checksum_length (v : Bech32.Variant) (hrp : List Char) (vals : List Nat) :
    (Bech32.checksum v hrp vals).length = 6 := by
  simp [Bech32.checksum]

/-- A string that ends in `p` (value 1) ends in the value 1. -/
theorem fin_final_p {s : List Char} {v : Bech32.Variant} {hrp : List Char} {vals : List Nat}
    (hv : Spec.Valid s v hrp vals) (p : List Char) (hp : s.map Spec.lower = p ++ ['p']) :
    ∃ vals₀, vals = vals₀ ++ [1] ∧ p = hrp ++ ['1'] ++ vals₀.map Spec.dataChar := by
  have hd := hv.data_length
  rcases List.eq_nil_or_concat vals with h | ⟨vals₀, z, rfl⟩
  · subst h; simp at hd
  · have e := hv.parts
    rw [hp, List.concat_eq_append, List.map_append, ← List.append_assoc] at e
    obtain ⟨e1, e2⟩ := List.append_inj' e (by simp)
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at e2
    have hz : z < 32 := hv.values_lt z (by simp)
    have : z = 1 := fin_dataChar_inj z 1 hz (by decide) (by rw [← e2]; rfl)
    subst this
    exact ⟨vals₀, List.concat_eq_append .., e1⟩

/-- A list with a `1` splits at its last `1`. -/
theorem fin_split_last_one (p : List Char) (hp : '1' ∈ p) :
    ∃ p₁ p₂, p = p₁ ++ '1' :: p₂ ∧ '1' ∉ p₂ := by
  cases h : Bech32.splitLast p with
  | none =>
    unfold Bech32.splitLast at h
    split at h
    · rename_i hi
      exact absurd (List.mem_reverse.2 hp) (List.idxOf?_eq_none_iff.1 hi)
    · cases h
  | some r =>
    obtain ⟨p₁, p₂⟩ := r
    exact ⟨p₁, p₂, (splitLast_eq_some_iff p p₁ p₂).1 h⟩

/-- The constants of two variants differ by 0 or by `1 ^^^ 0x2bc830a3`. -/
theorem fin_const_xor (v v' : Bech32.Variant) :
    v.const ^^^ v'.const = 0 ∨ v.const ^^^ v'.const = 1 ^^^ 0x2bc830a3 := by
  cases v <;> cases v' <;> decide

theorem fin_dataChar_zero : Spec.dataChar 0 = 'q' := rfl

theorem fin_dataChar_one : Spec.dataChar 1 = 'p' := rfl

theorem fin_xor_pos (a b : Nat) (h : a ≠ b) : 0 < a ^^^ b := by
  apply Nat.pos_of_ne_zero
  intro e
  rw [xor_eq_iff, Nat.xor_zero] at e
  exact h e.symm

/-! ## The statements -/

/-- `Spec.decode_encode`. -/
theorem decode_encode' (v : Bech32.Variant) (hrp : String) (data : List (Fin 32)) (s : String)
    (h : Bech32.encode v hrp data = some s) :
    Bech32.decode s = some (v, hrp, data) := by
  have hsome : (Bech32.encode v hrp data).isSome := by rw [h]; rfl
  have hc := (encode_isSome' v hrp data).1 hsome
  obtain ⟨hne, hchars, hlen⟩ := hc
  rw [fin_encode_eq v hrp data ⟨hne, hchars, hlen⟩, Option.some.injEq] at h
  subst h
  apply (decode_iff' _ v hrp data).2
  refine ⟨(Bech32.checksum v hrp.toList (data.map Fin.val)).map Fin.val,
    by simp [fin_checksum_length], ?_⟩
  have hpre : ∀ x ∈ Bech32.hrpExpand hrp.toList ++ data.map Fin.val, x < 32 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact fin_hrpExpand_lt _ (fun c hc => (hchars c hc).2.1) x hx
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      exact y.isLt
  apply fin_valid_of_lower
  · simp only [String.toList_ofList, List.length_append, List.length_cons, List.length_map,
      fin_checksum_length, String.length_toList]
    omega
  · exact fun c hc => ⟨⟨(hchars c hc).1, (hchars c hc).2.1⟩, (hchars c hc).2.2⟩
  · simp
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      exact y.isLt
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      exact y.isLt
  · exact hne
  · simp [fin_checksum_length]
  · rw [← polymod_eq, ← hrpExpand_eq, ← const_eq, ← List.append_assoc]
    exact ((checksum_iff v hrp.toList (data.map Fin.val) hpre _).2 rfl).2.2

/-- `Spec.encode_decode`. -/
theorem encode_decode' (s : String) (v : Bech32.Variant) (hrp : String) (data : List (Fin 32))
    (h : Bech32.decode s = some (v, hrp, data)) :
    (Bech32.encode v hrp data).map String.toList = some (s.toList.map Spec.lower) := by
  obtain ⟨check, hcl, hv⟩ := (decode_iff' s v hrp data).1 h
  have hhrp := fin_valid_hrp hv
  have hlt := hv.values_lt
  have hpre : ∀ x ∈ Bech32.hrpExpand hrp.toList ++ data.map Fin.val, x < 32 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact fin_hrpExpand_lt _ (fun c hc => (hhrp c hc).1.2) x hx
    · exact hlt x (List.mem_append_left _ hx)
  have hcheck : check = (Bech32.checksum v hrp.toList (data.map Fin.val)).map Fin.val := by
    apply (checksum_iff v hrp.toList (data.map Fin.val) hpre check).1
    refine ⟨hcl, fun x hx => hlt x (List.mem_append_right _ hx), ?_⟩
    rw [List.append_assoc, polymod_eq, hrpExpand_eq, const_eq]
    exact hv.checksum
  have hlen := fin_valid_length hv
  simp only [List.length_append, List.length_map, hcl] at hlen
  have hne : hrp.toList ≠ [] := List.length_pos_iff.1 hv.hrp_length.1
  rw [fin_encode_eq v hrp data ⟨hne, fun c hc => ⟨(hhrp c hc).1.1, (hhrp c hc).1.2,
    (hhrp c hc).2⟩, by have := hv.length; rw [← String.length_toList]; omega⟩,
    Option.map_some, String.toList_ofList, hv.parts, ← hcheck]
  simp

/-- `Spec.one_substitution`. -/
theorem one_substitution' (s s' : String) (p q : List Char) (x y : Char)
    (hp : '1' ∈ p) (hq : '1' ∉ q)
    (hx : x ∈ Spec.charset) (hy : y ∈ Spec.charset) (hxy : x ≠ y)
    (hs : s.toList.map Spec.lower = p ++ x :: q)
    (hs' : s'.toList.map Spec.lower = p ++ y :: q) :
    Bech32.decode s = none ∨ Bech32.decode s' = none := by
  obtain ⟨p₁, p₂, rfl, hp₂⟩ := fin_split_last_one p hp
  -- What a decoding of a string `p₁ ++ '1' :: p₂ ++ z :: q` looks like.
  have key : ∀ (t : String) (z : Char), z ∈ Spec.charset →
      t.toList.map Spec.lower = p₁ ++ '1' :: p₂ ++ z :: q →
      ∀ r, Bech32.decode t = some r →
      ∃ A a B, (∀ x ∈ A, x < 32) ∧ a < 32 ∧ (∀ x ∈ B, x < 32) ∧
        A.map Spec.dataChar = p₂ ∧ Spec.dataChar a = z ∧ B.map Spec.dataChar = q ∧
        B.length ≤ 88 ∧
        (∀ c ∈ p₁, c.toNat ≤ 126) ∧
        Bech32.polymod (Bech32.hrpExpand p₁ ++ A ++ a :: B) = r.1.const := by
    intro t z hz ht r hr
    obtain ⟨v, hrp, data⟩ := r
    obtain ⟨check, -, hv⟩ := (decode_iff' t v hrp data).1 hr
    have hlen := fin_valid_length hv
    have hl90 := hv.length
    have h1 := hv.hrp_length.1
    have e := hv.parts
    rw [ht, List.append_assoc, List.cons_append, List.append_assoc,
      List.singleton_append] at e
    have hz1 : z ≠ '1' := fun h => one_not_mem_charset (h ▸ hz)
    obtain ⟨e1, e2⟩ := split_unique _ _ _ _
      (by simp [hp₂, hq, Ne.symm hz1])
      (one_not_mem_map_dataChar _ hv.values_lt) e
    subst e1
    obtain ⟨A, R, hAR, hA, hR⟩ := List.map_eq_append_iff.1 e2.symm
    obtain ⟨a, B, rfl, ha, hB⟩ := List.map_eq_cons_iff.1 hR
    have hlt := hv.values_lt
    rw [hAR] at hlt hlen
    simp only [List.length_append, List.length_cons] at hlen
    refine ⟨A, a, B, fun x hx => hlt x (by simp [hx]), hlt a (by simp),
      fun x hx => hlt x (by simp [hx]), hA, ha, hB, by omega,
      fun c hc => (fin_valid_hrp hv c hc).1.2, ?_⟩
    have := hv.checksum
    rw [hAR, ← polymod_eq, ← hrpExpand_eq, ← const_eq] at this
    simpa [List.append_assoc] using this
  cases hr : Bech32.decode s with
  | none => exact Or.inl rfl
  | some r =>
  cases hr' : Bech32.decode s' with
  | none => exact Or.inr rfl
  | some r' =>
  exfalso
  obtain ⟨A, a, B, hA, ha, hB, hAm, hax, hBm, hBl, hp₁, hsum⟩ :=
    key s x hx hs r hr
  obtain ⟨A', b, B', hA', hb, hB', hAm', hby, hBm', -, -, hsum'⟩ :=
    key s' y hy hs' r' hr'
  have eA : A' = A := fin_map_dataChar_inj _ _ hA' hA (by rw [hAm, hAm'])
  have eB : B' = B := fin_map_dataChar_inj _ _ hB' hB (by rw [hBm, hBm'])
  subst eA eB
  have hab : a ≠ b := fun h => hxy (by rw [← hax, ← hby, h])
  have hpre : ∀ v ∈ Bech32.hrpExpand p₁ ++ A', v < 32 := by
    intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · exact fin_hrpExpand_lt p₁ hp₁ v hv
    · exact hA' v hv
  have hsub := polymod_subst (Bech32.hrpExpand p₁ ++ A') B' a b hpre hB ha hb
  rw [hsum, hsum'] at hsub
  have herr := single_error (a ^^^ b) B'.length (fin_xor_pos a b hab)
    (Nat.xor_lt_two_pow (n := 5) ha hb) hBl
  rcases fin_const_xor r.1 r'.1 with h0 | h0
  · exact herr.1 (hsub ▸ h0)
  · exact herr.2 (hsub ▸ h0)

/-- `Spec.insert_q_bech32`. -/
theorem insert_q_bech32' (s : String) (hrp : String) (data : List (Fin 32)) (p : List Char)
    (h : Bech32.decode s = some (.bech32, hrp, data))
    (hp : s.toList.map Spec.lower = p ++ ['p']) (hlen : s.length < 90) :
    ∃ data', Bech32.decode (String.ofList (p ++ ['q', 'p'])) = some (.bech32, hrp, data') := by
  obtain ⟨check, -, hv⟩ := (decode_iff' s _ hrp data).1 h
  obtain ⟨vals₀, hvals, hp'⟩ := fin_final_p hv p hp
  have hlt := hv.values_lt
  rw [hvals] at hlt
  have hpre : ∀ x ∈ Bech32.hrpExpand hrp.toList ++ vals₀, x < 32 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact fin_hrpExpand_lt _ (fun c hc => (fin_valid_hrp hv c hc).1.2) x hx
    · exact hlt x (by simp [hx])
  have hsum := hv.checksum
  rw [hvals, ← polymod_eq, ← hrpExpand_eq, ← const_eq, ← List.append_assoc] at hsum
  have hsum' := insert_bech32 _ hsum
  have hl := congrArg List.length hp
  simp only [List.length_map, List.length_append, List.length_singleton,
    String.length_toList] at hl
  have hd := hv.data_length
  rw [hvals] at hd
  simp only [List.length_append, List.length_singleton] at hd
  apply fin_decode_of_valid _ _ hrp (vals₀ ++ [0, 1])
  apply fin_valid_of_lower
  · simp only [String.toList_ofList, List.length_append, List.length_cons, List.length_nil]
    omega
  · exact fin_valid_hrp hv
  · rw [String.toList_ofList, hp']
    simp [fin_dataChar_zero, fin_dataChar_one]
  · intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | rfl | rfl
    · exact hlt x (by simp [hx])
    · decide
    · decide
  · exact List.length_pos_iff.1 hv.hrp_length.1
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [← polymod_eq, ← hrpExpand_eq, ← const_eq, ← List.append_assoc]
    exact hsum'

/-- `Spec.insert_q_bech32m`. -/
theorem insert_q_bech32m' (s : String) (hrp : String) (data : List (Fin 32)) (p : List Char)
    (h : Bech32.decode s = some (.bech32m, hrp, data))
    (hp : s.toList.map Spec.lower = p ++ ['p']) :
    Bech32.decode (String.ofList (p ++ ['q', 'p'])) = none := by
  obtain ⟨check, -, hv⟩ := (decode_iff' s _ hrp data).1 h
  obtain ⟨vals₀, hvals, hp'⟩ := fin_final_p hv p hp
  have hlt := hv.values_lt
  rw [hvals] at hlt
  have hsum := hv.checksum
  rw [hvals, ← polymod_eq, ← hrpExpand_eq, ← const_eq, ← List.append_assoc] at hsum
  have hbad := insert_bech32m _ hsum
  cases ht : Bech32.decode (String.ofList (p ++ ['q', 'p'])) with
  | none => rfl
  | some r =>
    exfalso
    obtain ⟨v', hrp', data'⟩ := r
    obtain ⟨check', -, hv'⟩ := (decode_iff' _ v' hrp' data').1 ht
    have e := hv'.parts
    have hlow : ∀ c ∈ p ++ ['q', 'p'], ¬ Spec.Upper c := by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | rfl | rfl
      · have hc' : c ∈ s.toList.map Spec.lower := by rw [hp]; simp [hc]
        exact (fin_mem_map_lower _ hv.range c hc').2
      · unfold Spec.Upper; decide
      · unfold Spec.Upper; decide
    rw [String.toList_ofList, fin_map_lower_of_not_upper _ hlow, hp'] at e
    have e' : hrp.toList ++ '1' :: (vals₀ ++ [0, 1]).map Spec.dataChar =
        hrp'.toList ++ '1' :: (data'.map Fin.val ++ check').map Spec.dataChar := by
      simpa [fin_dataChar_zero, fin_dataChar_one] using e
    have hlt0 : ∀ x ∈ vals₀ ++ [0, 1], x < 32 := by
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | rfl | rfl
      · exact hlt x (by simp [hx])
      · decide
      · decide
    obtain ⟨e1, e2⟩ := split_unique _ _ _ _ (one_not_mem_map_dataChar _ hlt0)
      (one_not_mem_map_dataChar _ hv'.values_lt) e'
    have e3 := fin_map_dataChar_inj _ _ hlt0 hv'.values_lt e2
    have hsum' := hv'.checksum
    rw [← e3, ← e1, ← polymod_eq, ← hrpExpand_eq, ← const_eq, ← List.append_assoc] at hsum'
    cases v' with
    | bech32 => exact hbad.1 hsum'
    | bech32m => exact hbad.2 hsum'

end Bech32.Proofs
