/-
  Decoding and encoding against the specification.

  The code's checksum (`polymodStep`, unrolled) is the BIP's loop
  (`polymod_eq`), the code's lower case is `Spec.lower` (`toLower_eq`),
  the code's data characters are `Spec.charset`, and `splitLast` finds
  the separator. From these, `decode` succeeds exactly on the strings
  `Spec.Decodes` describes (`decode_iff'`), and `encode` succeeds
  exactly when its human-readable part and length allow it
  (`encode_isSome'`), writing no upper case letter (`encode_lower'`).
-/

import Spec.Defs

namespace Bech32.Proofs

/-! ## The checksum

`b &&& 2 ^ i = 0` (the code) and `(b >>> i) &&& 1 = 1` (the BIP) test
the same bit. -/

theorem and_two_pow_eq_zero_iff (b i : Nat) : b &&& 2 ^ i = 0 ↔ b.testBit i = false := by
  constructor
  · intro h
    have := congrArg (fun x => Nat.testBit x i) h
    simpa [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hij : i = j
    · subst hij; simp [h]
    · simp [hij]

theorem shiftRight_and_one_eq_one_iff (b i : Nat) :
    (b >>> i) &&& 1 = 1 ↔ b.testBit i = true := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  simp

theorem ite_bit (b i c g : Nat) :
    (if b &&& 2 ^ i = 0 then c else c ^^^ g) =
      c ^^^ (if (b >>> i) &&& 1 = 1 then g else 0) := by
  have h1 := and_two_pow_eq_zero_iff b i
  have h2 := shiftRight_and_one_eq_one_iff b i
  cases hb : b.testBit i
  · have e1 : b &&& 2 ^ i = 0 := h1.2 hb
    have e2 : ¬ (b >>> i &&& 1 = 1) := by rw [h2, hb]; decide
    simp only [e1, e2, ↓reduceIte, Nat.xor_zero]
  · have e1 : ¬ (b &&& 2 ^ i = 0) := by rw [h1, hb]; decide
    have e2 : b >>> i &&& 1 = 1 := h2.2 hb
    simp only [e1, e2, ↓reduceIte]

/-- One step of the code's checksum is the loop body of `bech32_polymod`. -/
theorem polymodStep_eq_spec (chk v : Nat) :
    Bech32.polymodStep chk v =
      (List.range 5).foldl
        (fun c i => c ^^^ (if ((chk >>> 25) >>> i) &&& 1 = 1 then Spec.GEN.getD i 0 else 0))
        (((chk &&& 0x1ffffff) <<< 5) ^^^ v) := by
  have e0 := ite_bit (chk >>> 25) 0
  have e1 := ite_bit (chk >>> 25) 1
  have e2 := ite_bit (chk >>> 25) 2
  have e3 := ite_bit (chk >>> 25) 3
  have e4 := ite_bit (chk >>> 25) 4
  simp only [Nat.reducePow] at e0 e1 e2 e3 e4
  simp only [Bech32.polymodStep, e0, e1, e2, e3, e4]
  rfl

/-- The code's checksum is BIP 173's `bech32_polymod`. -/
theorem polymod_eq (vs : List Nat) : Bech32.polymod vs = Spec.polymod vs := by
  unfold Bech32.polymod Spec.polymod
  congr 1
  funext chk v
  exact polymodStep_eq_spec chk v

/-- The code's HRP expansion is BIP 173's `bech32_hrp_expand`. -/
theorem hrpExpand_eq (s : List Char) : Bech32.hrpExpand s = Spec.hrpExpand s := rfl

/-! ## Characters -/

theorem upper_iff (c : Char) : Spec.Upper c ↔ 65 ≤ c.toNat ∧ c.toNat ≤ 90 := by
  simp only [Spec.Upper, Char.le_def, UInt32.le_iff_toNat_le, Char.toNat_val]
  rfl

theorem lower_iff (c : Char) : Spec.Lower c ↔ 97 ≤ c.toNat ∧ c.toNat ≤ 122 := by
  simp only [Spec.Lower, Char.le_def, UInt32.le_iff_toNat_le, Char.toNat_val]
  rfl

theorem isUpper_iff (c : Char) : Bech32.isUpper c = true ↔ Spec.Upper c := by
  simp [Bech32.isUpper, Spec.Upper]

theorem isLower_iff (c : Char) : Bech32.isLower c = true ↔ Spec.Lower c := by
  simp [Bech32.isLower, Spec.Lower]

theorem isPrintable_iff (c : Char) :
    Bech32.isPrintable c = true ↔ 33 ≤ c.toNat ∧ c.toNat ≤ 126 := by
  simp [Bech32.isPrintable]

/-- The code's lower case is `Spec.lower`. -/
theorem toLower_eq : Bech32.toLower = Spec.lower := by
  funext c
  simp only [Bech32.toLower, Spec.lower, Bech32.isUpper, Bool.and_eq_true, decide_eq_true_eq]

theorem toNat_ofNat_of_lt (n : Nat) (h : n < 0xd800) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl h
  simp only [Char.ofNat, hv, ↓reduceDIte, Char.ofNatAux, Char.toNat_mk]
  rfl

theorem lower_toNat_of_upper (c : Char) (h : Spec.Upper c) :
    (Spec.lower c).toNat = c.toNat + 32 := by
  have := (upper_iff c).1 h
  have h' : 'A' ≤ c ∧ c ≤ 'Z' := h
  simp only [Spec.lower, h', and_self, ↓reduceIte]
  exact toNat_ofNat_of_lt _ (by omega)

theorem lower_of_not_upper (c : Char) (h : ¬ Spec.Upper c) : Spec.lower c = c := by
  have h' : ¬ ('A' ≤ c ∧ c ≤ 'Z') := h
  simp only [Spec.lower, h', ↓reduceIte]

/-- `Spec.lower` keeps characters in the range 33 to 126. -/
theorem lower_range (c : Char) (h : 33 ≤ c.toNat ∧ c.toNat ≤ 126) :
    33 ≤ (Spec.lower c).toNat ∧ (Spec.lower c).toNat ≤ 126 := by
  by_cases hc : Spec.Upper c
  · have := (upper_iff c).1 hc
    rw [lower_toNat_of_upper c hc]; omega
  · rw [lower_of_not_upper c hc]; exact h

/-- No `Spec.lower c` is an upper case letter. -/
theorem not_upper_lower (c : Char) : ¬ Spec.Upper (Spec.lower c) := by
  by_cases hc : Spec.Upper c
  · have := (upper_iff c).1 hc
    rw [upper_iff, lower_toNat_of_upper c hc]; omega
  · rw [lower_of_not_upper c hc]; exact hc

theorem lower_lower (c : Char) : Spec.lower (Spec.lower c) = Spec.lower c :=
  lower_of_not_upper _ (not_upper_lower c)

/-! ## The data characters -/

/-- The code's data characters are those of the BIP. -/
theorem charset_eq : Bech32.charset = Spec.charset := by decide

/-- The code writes a value as `Spec.dataChar` does. -/
theorem charOf_eq (v : Fin 32) : Bech32.charOf v = Spec.dataChar v.val := by
  unfold Bech32.charOf Spec.dataChar
  rw [charset_eq]

theorem charset_length : Spec.charset.length = 32 := rfl

theorem dataChar_mem (n : Nat) (h : n < 32) : Spec.dataChar n ∈ Spec.charset := by
  unfold Spec.dataChar
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [charset_length]; exact h)]
  exact List.getElem_mem _

theorem one_not_mem_charset : '1' ∉ Spec.charset := by decide

theorem charset_not_upper : ∀ c ∈ Spec.charset, ¬ Spec.Upper c := by
  unfold Spec.Upper; decide

theorem charset_range : ∀ c ∈ Spec.charset, 33 ≤ c.toNat ∧ c.toNat ≤ 126 := by decide

/-- `valueOf` reads back each data character. -/
theorem valueOf_dataChar : ∀ x : Fin 32, Bech32.valueOf (Spec.dataChar x.val) = some x := by
  decide

theorem mem_charset_of_valueOf (c : Char) (x : Fin 32) (h : Bech32.valueOf c = some x) :
    c ∈ Spec.charset := by
  simp only [Bech32.valueOf] at h
  split at h
  · rename_i hlt
    rw [← charset_eq]
    rw [charset_eq] at hlt
    exact List.idxOf_lt_length_iff.1 (by rw [charset_eq, charset_length]; exact hlt)
  · cases h

/-- `valueOf c = some x` exactly when `c` is the data character of `x`. -/
theorem valueOf_eq_some_iff (c : Char) (x : Fin 32) :
    Bech32.valueOf c = some x ↔ Spec.dataChar x.val = c := by
  constructor
  · intro h
    have hm := mem_charset_of_valueOf c x h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    have e : Spec.dataChar i = Spec.charset[i] := by
      unfold Spec.dataChar
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    have := valueOf_dataChar ⟨i, hi⟩
    simp only [e] at this
    rw [this] at h
    cases h
    exact e
  · rintro rfl
    exact valueOf_dataChar x

/-- `valueOf` fails exactly on the characters that are not data characters. -/
theorem valueOf_eq_none_iff (c : Char) : Bech32.valueOf c = none ↔ c ∉ Spec.charset := by
  constructor
  · intro h hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    have e : Spec.dataChar i = Spec.charset[i] := by
      unfold Spec.dataChar
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    have := valueOf_dataChar ⟨i, hi⟩
    simp only [e] at this
    rw [this] at h
    cases h
  · intro h
    cases hv : Bech32.valueOf c with
    | none => rfl
    | some x => exact absurd (mem_charset_of_valueOf c x hv) h

/-- The data part reads as the values `d` exactly when it is their data characters. -/
theorem mapM_valueOf_eq_some_iff (cs : List Char) (d : List (Fin 32)) :
    cs.mapM Bech32.valueOf = some d ↔ cs = d.map (fun x => Spec.dataChar x.val) := by
  induction cs generalizing d with
  | nil =>
    cases d <;> simp
  | cons c cs ih =>
    cases d with
    | nil =>
      simp [List.mapM_cons, Option.bind_eq_some_iff]
    | cons x xs =>
      simp [List.mapM_cons, Option.bind_eq_some_iff, ih, valueOf_eq_some_iff]
      intro _; exact eq_comm

/-- No data character is the separator. -/
theorem one_not_mem_map_dataChar (vals : List Nat) (h : ∀ x ∈ vals, x < 32) :
    '1' ∉ vals.map Spec.dataChar := by
  intro hm
  obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
  exact one_not_mem_charset (e ▸ dataChar_mem x (h x hx))

/-! ## Splitting at the last separator -/

theorem idxOf?_eq_some_iff_split {α : Type} [BEq α] [LawfulBEq α] (a : α) (l : List α)
    (i : Nat) :
    l.idxOf? a = some i ↔ ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = i ∧ a ∉ l₁ := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    rw [List.idxOf?_cons]
    by_cases hb : b = a
    · subst hb
      simp only [BEq.rfl, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨[], l, by simp⟩
      · rintro ⟨l₁, l₂, h1, h2, h3⟩
        cases l₁ with
        | nil => simpa using h2
        | cons c l₁ =>
          simp only [List.cons_append, List.cons.injEq] at h1
          exact absurd (h1.1 ▸ List.mem_cons_self) h3
    · have hb' : (b == a) = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff]
      constructor
      · rintro ⟨j, hj, rfl⟩
        obtain ⟨l₁, l₂, h1, h2, h3⟩ := (ih j).1 hj
        refine ⟨b :: l₁, l₂, by simp [h1], by simp [h2], ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => hb h.symm, h3⟩
      · rintro ⟨l₁, l₂, h1, h2, h3⟩
        cases l₁ with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at h1
          exact absurd h1.1 hb
        | cons c l₁ =>
          simp only [List.cons_append, List.cons.injEq] at h1
          obtain ⟨rfl, h1⟩ := h1
          refine ⟨l₁.length,
            (ih _).2 ⟨l₁, l₂, h1, rfl, fun h => h3 (List.mem_cons_of_mem _ h)⟩, ?_⟩
          simpa using h2

/-- `splitLast` splits at the last `1`. -/
theorem splitLast_append (h r : List Char) (hr : '1' ∉ r) :
    Bech32.splitLast (h ++ '1' :: r) = some (h, r) := by
  have hi : (h ++ '1' :: r).reverse.idxOf? '1' = some r.length := by
    rw [idxOf?_eq_some_iff_split]
    exact ⟨r.reverse, h.reverse, by simp, by simp, by simpa using hr⟩
  unfold Bech32.splitLast
  rw [hi]
  simp only [List.length_append, List.length_cons, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rw [List.take_left']; omega
  · rw [show h.length + (r.length + 1) - r.length = (h ++ ['1']).length by simp; omega,
      show h ++ '1' :: r = (h ++ ['1']) ++ r by simp, List.drop_left]

/-- What `splitLast` gives: the parts before and after a `1` with no `1` after it. -/
theorem splitLast_eq_some_iff (cs h r : List Char) :
    Bech32.splitLast cs = some (h, r) ↔ cs = h ++ '1' :: r ∧ '1' ∉ r := by
  constructor
  · intro hs
    unfold Bech32.splitLast at hs
    split at hs
    · cases hs
    · rename_i i hi
      obtain ⟨l₁, l₂, h1, h2, h3⟩ := (idxOf?_eq_some_iff_split _ _ _).1 hi
      have hcs : cs = l₂.reverse ++ '1' :: l₁.reverse := by
        rw [← List.reverse_reverse cs, h1]; simp
      have := splitLast_append l₂.reverse l₁.reverse (by simpa using h3)
      rw [← hcs] at this
      unfold Bech32.splitLast at this
      rw [hi] at this
      dsimp only at this
      rw [this] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨hcs, by simpa using h3⟩
  · rintro ⟨rfl, hr⟩
    exact splitLast_append h r hr

/-- A list has at most one split at a `1` with no `1` after it. -/
theorem split_unique (h r h' r' : List Char) (hr : '1' ∉ r) (hr' : '1' ∉ r')
    (e : h ++ '1' :: r = h' ++ '1' :: r') : h = h' ∧ r = r' := by
  have e1 := splitLast_append h r hr
  rw [e, splitLast_append h' r' hr'] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  exact ⟨e1.1.symm, e1.2.symm⟩

/-- `split_unique` in the form `Spec.Valid.parts` uses. -/
theorem split_unique' (h r h' r' : List Char) (hr : '1' ∉ r) (hr' : '1' ∉ r')
    (e : h ++ ['1'] ++ r = h' ++ ['1'] ++ r') : h = h' ∧ r = r' := by
  simp only [List.append_assoc, List.singleton_append] at e
  exact split_unique h r h' r' hr hr' e

/-! ## Lists of values -/

theorem exists_fin_list (l : List Nat) (h : ∀ x ∈ l, x < 32) :
    ∃ l' : List (Fin 32), l'.map Fin.val = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨l', hl'⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact ⟨⟨x, h x List.mem_cons_self⟩ :: l', by simp [hl']⟩

/-! ## The checksum variant -/

/-- The code's constants are those of the BIPs. -/
theorem const_eq (v : Bech32.Variant) : v.const = Spec.const v := by
  cases v <;> rfl

/-- `variantOf` gives the variant whose constant the checksum gives. -/
theorem variantOf_eq_some_iff (hrp : List Char) (vals : List Nat) (v : Bech32.Variant) :
    Bech32.variantOf hrp vals = some v ↔
      Spec.polymod (Spec.hrpExpand hrp ++ vals) = Spec.const v := by
  rw [← polymod_eq, ← hrpExpand_eq, ← const_eq]
  simp only [Bech32.variantOf]
  generalize Bech32.polymod (Bech32.hrpExpand hrp ++ vals) = pm
  cases v
  · by_cases h1 : pm = 1
    · simp [h1, Bech32.Variant.const]
    · by_cases h2 : pm = 0x2bc830a3
      · simp [h2, Bech32.Variant.const]
      · simp [h1, h2, Bech32.Variant.const]
  · by_cases h1 : pm = 1
    · simp [h1, Bech32.Variant.const]
    · by_cases h2 : pm = 0x2bc830a3
      · simp [h2, Bech32.Variant.const]
      · simp [h1, h2, Bech32.Variant.const]

/-! ## Decoding -/

/-- What `decode` accepts is valid. -/
theorem decode_some {s : String} {v : Bech32.Variant} {hrp : String} {data : List (Fin 32)}
    (h : Bech32.decode s = some (v, hrp, data)) :
    Spec.Decodes s.toList v hrp.toList (data.map Fin.val) := by
  simp only [Bech32.decode] at h
  split at h
  · cases h
  · rename_i hcond
    split at h
    · cases h
    · rename_i hh rest hsplit
      split at h
      · cases h
      · rename_i hne
        split at h
        · cases h
        · rename_i d hmap
          split at h
          · cases h
          · rename_i v' hv
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_true,
              not_or, Nat.not_lt] at hcond
            obtain ⟨⟨hlen, hall⟩, hmix⟩ := hcond
            simp only [Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff, not_or,
              Nat.not_lt] at hne
            obtain ⟨hne, hrest⟩ := hne
            obtain ⟨hsplit, -⟩ := (splitLast_eq_some_iff _ _ _).1 hsplit
            rw [toLower_eq] at hsplit
            have hmap := (mapM_valueOf_eq_some_iff _ _).1 hmap
            have hv := (variantOf_eq_some_iff _ _ _).1 hv
            have hl := congrArg List.length hsplit
            have hd := congrArg List.length hmap
            simp only [List.length_map, List.length_append, List.length_cons] at hl hd
            rw [String.toList_ofList]
            refine ⟨(d.drop (d.length - 6)).map Fin.val, by simp; omega, ?_⟩
            rw [← List.map_append, List.take_append_drop]
            exact {
              length := hlen
              range := by
                intro c hc
                have hall' : s.toList.all Bech32.isPrintable = true := by simpa using hall
                exact (isPrintable_iff c).1 (List.all_eq_true.1 hall' c hc)
              not_mixed := by
                rintro ⟨⟨c, hc, hu⟩, ⟨c', hc', hlo⟩⟩
                exact hmix ⟨List.any_eq_true.2 ⟨c, hc, (isUpper_iff c).2 hu⟩,
                  List.any_eq_true.2 ⟨c', hc', (isLower_iff c').2 hlo⟩⟩
              parts := by
                rw [hsplit, hmap, List.map_map]
                simp
              values_lt := by
                intro x hx
                obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
                exact y.isLt
              hrp_length := ⟨List.length_pos_iff.2 hne, by omega⟩
              data_length := by simp; omega
              checksum := hv }

/-- What is valid, `decode` accepts. -/
theorem decode_of_decodes {s : String} {v : Bech32.Variant} {hrp : String}
    {data : List (Fin 32)} (h : Spec.Decodes s.toList v hrp.toList (data.map Fin.val)) :
    Bech32.decode s = some (v, hrp, data) := by
  obtain ⟨check, hcl, hv⟩ := h
  obtain ⟨check', rfl⟩ := exists_fin_list check
    (fun x hx => hv.values_lt x (List.mem_append_right _ hx))
  rw [← List.map_append] at hv
  have hsplit : Bech32.splitLast (s.toList.map Bech32.toLower) =
      some (hrp.toList, (data ++ check').map (fun x => Spec.dataChar x.val)) := by
    rw [toLower_eq, hv.parts, List.map_map, List.append_assoc, List.singleton_append]
    apply splitLast_append
    intro hm
    obtain ⟨x, -, hx⟩ := List.mem_map.1 hm
    exact one_not_mem_charset (hx ▸ dataChar_mem _ x.isLt)
  have hmap : ((data ++ check').map (fun x => Spec.dataChar x.val)).mapM Bech32.valueOf =
      some (data ++ check') := (mapM_valueOf_eq_some_iff _ _).2 rfl
  have hvar : Bech32.variantOf hrp.toList ((data ++ check').map Fin.val) = some v :=
    (variantOf_eq_some_iff _ _ _).2 hv.checksum
  have hlen := hv.length
  have hall : s.toList.all Bech32.isPrintable = true :=
    List.all_eq_true.2 fun c hc => (isPrintable_iff c).2 (hv.range c hc)
  have hmix : ¬ (s.toList.any Bech32.isUpper = true ∧ s.toList.any Bech32.isLower = true) := by
    rintro ⟨hu, hlo⟩
    obtain ⟨c, hc, hu⟩ := List.any_eq_true.1 hu
    obtain ⟨c', hc', hlo⟩ := List.any_eq_true.1 hlo
    exact hv.not_mixed ⟨⟨c, hc, (isUpper_iff c).1 hu⟩, ⟨c', hc', (isLower_iff c').1 hlo⟩⟩
  have hne : hrp.toList ≠ [] := List.length_pos_iff.1 hv.hrp_length.1
  have hdl := hv.data_length
  simp only [List.length_map] at hdl
  simp only [List.length_map] at hcl
  have c1 : ¬ ((decide (90 < s.toList.length) || !s.toList.all Bech32.isPrintable ||
      (s.toList.any Bech32.isUpper && s.toList.any Bech32.isLower)) = true) := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_true, not_or,
      Nat.not_lt, hall]
    exact ⟨⟨hlen, Bool.noConfusion⟩, hmix⟩
  have c2 : ¬ ((hrp.toList.isEmpty ||
      decide (((data ++ check').map (fun x => Spec.dataChar x.val)).length < 6)) = true) := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff, not_or, Nat.not_lt,
      List.length_map]
    exact ⟨hne, hdl⟩
  simp only [Bech32.decode]
  rw [ite_eq_right_of_eq_false _ _ (eq_false c1), hsplit]
  dsimp only
  rw [ite_eq_right_of_eq_false _ _ (eq_false c2), hmap]
  dsimp only
  rw [hvar]
  dsimp only
  rw [String.ofList_toList, List.take_left' (by simp [hcl])]

/-- `Spec.decode_iff`. -/
theorem decode_iff' (s : String) (v : Bech32.Variant) (hrp : String) (data : List (Fin 32)) :
    Bech32.decode s = some (v, hrp, data) ↔
      Spec.Decodes s.toList v hrp.toList (data.map Fin.val) :=
  ⟨decode_some, decode_of_decodes⟩

/-! ## Encoding -/

/-- The condition under which `encode` fails, negated. -/
theorem encode_cond_iff (hrp : String) (data : List (Fin 32)) :
    ¬ ((hrp.toList.isEmpty ||
        !hrp.toList.all (fun c => Bech32.isPrintable c && !Bech32.isUpper c) ||
        decide (90 < hrp.toList.length + 7 + data.length)) = true) ↔
      hrp.toList ≠ [] ∧
      (∀ c ∈ hrp.toList, 33 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ ¬ Spec.Upper c) ∧
      hrp.length + 1 + data.length + 6 ≤ 90 := by
  simp only [Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_true', decide_eq_true_eq, not_or,
    Nat.not_lt, Bool.not_eq_false, List.all_eq_true, Bool.and_eq_true, isPrintable_iff,
    Bool.not_eq_true', ← isUpper_iff, String.length_toList]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun c hc => ?_, by omega⟩
    obtain ⟨⟨a, b⟩, d⟩ := h2 c hc
    exact ⟨a, b, by simp [d]⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, fun c hc => ?_⟩, by omega⟩
    obtain ⟨a, b, d⟩ := h2 c hc
    exact ⟨⟨a, b⟩, by simpa using d⟩

/-- `Spec.encode_isSome`. -/
theorem encode_isSome' (v : Bech32.Variant) (hrp : String) (data : List (Fin 32)) :
    (Bech32.encode v hrp data).isSome ↔
      hrp.toList ≠ [] ∧
      (∀ c ∈ hrp.toList, 33 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ ¬ Spec.Upper c) ∧
      hrp.length + 1 + data.length + 6 ≤ 90 := by
  rw [← encode_cond_iff]
  simp only [Bech32.encode]
  split
  · rename_i hc
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, Decidable.not_not]
    exact hc
  · rename_i hc
    simp only [Option.isSome_some, true_iff]
    exact hc

/-- `Spec.encode_lower`. -/
theorem encode_lower' (v : Bech32.Variant) (hrp : String) (data : List (Fin 32)) (s : String)
    (h : Bech32.encode v hrp data = some s) :
    ∀ c ∈ s.toList, ¬ Spec.Upper c := by
  simp only [Bech32.encode] at h
  split at h
  · cases h
  · rename_i hc
    obtain ⟨-, hc, -⟩ := (encode_cond_iff hrp data).1 hc
    simp only [Option.some.injEq] at h
    subst h
    rw [String.toList_ofList]
    intro c hc'
    simp only [List.mem_append, List.mem_cons, List.mem_map] at hc'
    rcases hc' with hin | rfl | ⟨x, -, rfl⟩
    · exact (hc c hin).2.2
    · unfold Spec.Upper; decide
    · rw [charOf_eq]
      exact charset_not_upper _ (dataChar_mem _ x.isLt)

end Bech32.Proofs
