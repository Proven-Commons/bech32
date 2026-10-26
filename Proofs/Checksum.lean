/-
  The Bech32 checksum as a linear map.

  `polymodStep c v` is multiplication by `x` modulo the BIP 173
  generator, plus `v`: on states below `2 ^ 30` it is
  `T c ^^^ v` with `T` xor-linear. From that come the statements
  about changing one value, about the six checksum values being
  determined, and about inserting a `q` before a final `p`.
-/

import Bech32

namespace Bech32.Proofs

open Bech32

/-- `f^[n] x` is `f` applied `n` times to `x`. This is Mathlib's notation for
    `Nat.iterate`; core Lean has no `Nat.iterate`, so here it stands for core's
    `Nat.repeat`, which is the same function. -/
scoped notation:max f "^[" n "]" => Nat.repeat f n

theorem repeat_zero (f : Nat → Nat) (x : Nat) : f^[0] x = x := rfl

theorem repeat_succ' (f : Nat → Nat) (n x : Nat) : f^[n + 1] x = f (f^[n] x) := rfl

theorem repeat_succ (f : Nat → Nat) (n x : Nat) : f^[n + 1] x = f^[n] (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeat_succ', ih, repeat_succ']

/-- One step with the value 0: multiplication by x modulo the generator. -/
def T (c : Nat) : Nat := Bech32.polymodStep c 0

/-! ### Xor as a commutative monoid -/

local instance : Std.Associative (α := Nat) (· ^^^ ·) := ⟨Nat.xor_assoc⟩
local instance : Std.Commutative (α := Nat) (· ^^^ ·) := ⟨Nat.xor_comm⟩

theorem xor_cancel_right (a b c : Nat) : (a ^^^ c) ^^^ (b ^^^ c) = a ^^^ b := by
  rw [Nat.xor_assoc, ← Nat.xor_assoc c, Nat.xor_comm c b, Nat.xor_assoc, Nat.xor_self,
    Nat.xor_zero]

theorem xor_eq_iff (a b c : Nat) : a ^^^ b = c ↔ b = a ^^^ c := by
  constructor
  · intro h; subst h; rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · intro h; subst h; rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-! ### One step -/

/-- The generator constants for the set bits of `b`. -/
def G (b : Nat) : Nat :=
  (if b &&& 1 = 0 then 0 else 0x3b6a57b2) ^^^
  (if b &&& 2 = 0 then 0 else 0x26508e6d) ^^^
  (if b &&& 4 = 0 then 0 else 0x1ea119fa) ^^^
  (if b &&& 8 = 0 then 0 else 0x3d4233dd) ^^^
  (if b &&& 16 = 0 then 0 else 0x2a1462b3)

theorem ite_xor (p : Prop) [Decidable p] (x g : Nat) :
    (if p then x else x ^^^ g) = x ^^^ (if p then 0 else g) := by
  split <;> simp

theorem polymodStep_eq (c v : Nat) :
    polymodStep c v = ((c &&& 0x1ffffff) <<< 5) ^^^ v ^^^ G (c >>> 25) := by
  simp only [polymodStep, ite_xor]
  simp only [G, Nat.xor_assoc]

theorem T_eq (c : Nat) : T c = ((c &&& 0x1ffffff) <<< 5) ^^^ G (c >>> 25) := by
  rw [T, polymodStep_eq, Nat.xor_zero]

theorem G_xor_all : ∀ b₁, b₁ < 32 → ∀ b₂, b₂ < 32 → G (b₁ ^^^ b₂) = G b₁ ^^^ G b₂ := by
  decide +kernel

theorem G_lt_all : ∀ b, b < 32 → G b < 2 ^ 30 := by
  decide +kernel

theorem shiftRight_25_lt (c : Nat) (hc : c < 2 ^ 30) : c >>> 25 < 32 := by
  rw [Nat.shiftRight_eq_div_pow]
  have : (2 : Nat) ^ 30 = 1073741824 := rfl
  have : (2 : Nat) ^ 25 = 33554432 := rfl
  omega

theorem polymodStep_lt (c v : Nat) (hc : c < 2 ^ 30) (hv : v < 32) :
    Bech32.polymodStep c v < 2 ^ 30 := by
  rw [polymodStep_eq]
  have h1 : (c &&& 0x1ffffff) < 2 ^ 25 := Nat.and_lt_two_pow c (by decide)
  have h2 : (c &&& 0x1ffffff) <<< 5 < 2 ^ 30 := by
    rw [Nat.shiftLeft_eq]
    have : (2 : Nat) ^ 30 = 1073741824 := rfl
    have : (2 : Nat) ^ 25 = 33554432 := rfl
    have : (2 : Nat) ^ 5 = 32 := rfl
    omega
  have h3 : v < 2 ^ 30 := Nat.lt_of_lt_of_le hv (by decide)
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h2 h3) (G_lt_all _ (shiftRight_25_lt c hc))

-- `hv` is not needed: the decomposition holds for every `v`.
set_option linter.unusedVariables false in
theorem polymodStep_xor (c v : Nat) (hv : v < 32) : Bech32.polymodStep c v = T c ^^^ v := by
  rw [polymodStep_eq, T_eq]
  ac_rfl

theorem T_lt (c : Nat) (hc : c < 2 ^ 30) : T c < 2 ^ 30 :=
  polymodStep_lt c 0 hc (by decide)

theorem T_xor (a b : Nat) (ha : a < 2 ^ 30) (hb : b < 2 ^ 30) : T (a ^^^ b) = T a ^^^ T b := by
  rw [T_eq, T_eq, T_eq, Nat.and_xor_distrib_right, Nat.shiftLeft_xor_distrib,
    Nat.shiftRight_xor_distrib, G_xor_all _ (shiftRight_25_lt a ha) _ (shiftRight_25_lt b hb)]
  ac_rfl

theorem T_zero : T 0 = 0 := by decide

/-! ### Lists of values -/

theorem polymod_append (a b : List Nat) :
    Bech32.polymod (a ++ b) = b.foldl Bech32.polymodStep (Bech32.polymod a) := by
  simp only [polymod, List.foldl_append]

theorem foldl_lt (vs : List Nat) (h : ∀ v ∈ vs, v < 32) (c : Nat) (hc : c < 2 ^ 30) :
    vs.foldl Bech32.polymodStep c < 2 ^ 30 := by
  induction vs generalizing c with
  | nil => exact hc
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact ih (fun v hv => h v (List.mem_cons_of_mem x hv)) _
      (polymodStep_lt c x hc (h x (List.mem_cons_self ..)))

theorem polymod_lt (vs : List Nat) (h : ∀ v ∈ vs, v < 32) : Bech32.polymod vs < 2 ^ 30 :=
  foldl_lt vs h 1 (by decide)

theorem T_iterate_lt (n c : Nat) (hc : c < 2 ^ 30) : T^[n] c < 2 ^ 30 := by
  induction n with
  | zero => exact hc
  | succ n ih => rw [repeat_succ']; exact T_lt _ ih

theorem T_iterate_xor (n a b : Nat) (ha : a < 2 ^ 30) (hb : b < 2 ^ 30) :
    T^[n] (a ^^^ b) = T^[n] a ^^^ T^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [repeat_succ', repeat_succ', repeat_succ',
      ih, T_xor _ _ (T_iterate_lt n a ha) (T_iterate_lt n b hb)]

/-- Two runs over the same values differ by `T`, once per value, applied to the
    difference of the starting states. -/
theorem foldl_xor (l : List Nat) (hl : ∀ v ∈ l, v < 32) (c₁ c₂ : Nat)
    (h₁ : c₁ < 2 ^ 30) (h₂ : c₂ < 2 ^ 30) :
    l.foldl Bech32.polymodStep c₁ ^^^ l.foldl Bech32.polymodStep c₂ = T^[l.length] (c₁ ^^^ c₂) := by
  induction l generalizing c₁ c₂ with
  | nil => rfl
  | cons x xs ih =>
    have hx : x < 32 := hl x (List.mem_cons_self ..)
    have hxs : ∀ v ∈ xs, v < 32 := fun v hv => hl v (List.mem_cons_of_mem x hv)
    rw [List.foldl_cons, List.foldl_cons, ih hxs _ _ (polymodStep_lt c₁ x h₁ hx)
      (polymodStep_lt c₂ x h₂ hx), polymodStep_xor _ _ hx, polymodStep_xor _ _ hx,
      xor_cancel_right, ← T_xor _ _ h₁ h₂, List.length_cons, repeat_succ]

/-- Changing one value changes the checksum by `T` applied, once per later value, to the difference. -/
theorem polymod_subst (a b : List Nat) (x y : Nat)
    (ha : ∀ v ∈ a, v < 32) (hb : ∀ v ∈ b, v < 32) (hx : x < 32) (hy : y < 32) :
    Bech32.polymod (a ++ x :: b) ^^^ Bech32.polymod (a ++ y :: b) = T^[b.length] (x ^^^ y) := by
  have hp := polymod_lt a ha
  rw [polymod_append, polymod_append, List.foldl_cons, List.foldl_cons,
    foldl_xor b hb _ _ (polymodStep_lt _ x hp hx) (polymodStep_lt _ y hp hy),
    polymodStep_xor _ _ hx, polymodStep_xor _ _ hy, Nat.xor_comm (T _) x, Nat.xor_comm (T _) y,
    xor_cancel_right]

/-! ### Single errors -/

/-- `okFrom x n`: none of `x, T x, …, T^[n] x` is 0 or `1 ^^^ 0x2bc830a3`. -/
def okFrom (x : Nat) : Nat → Bool
  | 0 => x != 0 && x != 1 ^^^ 0x2bc830a3
  | n + 1 => (x != 0 && x != 1 ^^^ 0x2bc830a3) && okFrom (T x) n

theorem okFrom_spec (n x : Nat) (h : okFrom x n = true) (m : Nat) (hm : m ≤ n) :
    T^[m] x ≠ 0 ∧ T^[m] x ≠ 1 ^^^ 0x2bc830a3 := by
  induction n generalizing x m with
  | zero =>
    have : m = 0 := by omega
    subst this
    simpa [okFrom, repeat_zero] using h
  | succ n ih =>
    simp only [okFrom, Bool.and_eq_true] at h
    cases m with
    | zero => simpa [repeat_zero] using h.1
    | succ m =>
      rw [repeat_succ]
      exact ih (T x) h.2 m (by omega)

theorem okFrom_all : ∀ e, e < 32 → 0 < e → okFrom e 88 = true := by
  decide +kernel

/-- A single error is never invisible, nor turns one variant's constant into the other's,
    for up to 88 later values. -/
theorem single_error (e m : Nat) (he : 0 < e) (he' : e < 32) (hm : m ≤ 88) :
    T^[m] e ≠ 0 ∧ T^[m] e ≠ 1 ^^^ 0x2bc830a3 :=
  okFrom_spec 88 e (okFrom_all e he' he) m hm

/-! ### The six checksum values -/

/-- A step from a state below `2 ^ 25` appends a 5-bit value. -/
theorem polymodStep_small (a v : Nat) (ha : a < 33554432) (hv : v < 32) :
    Bech32.polymodStep a v = a * 32 + v := by
  have hb : a >>> 25 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt ha
  have hm : a &&& 0x1ffffff = a := Nat.and_two_pow_sub_one_of_lt_two_pow (n := 25) ha
  have hG : G 0 = 0 := by decide
  rw [polymodStep_eq, hb, hm, hG, Nat.xor_zero]
  have hdiv : ((a <<< 5) ^^^ v) / 2 ^ 5 = a := by
    rw [Nat.xor_div_two_pow, Nat.shiftLeft_eq, Nat.mul_div_cancel _ (by decide),
      Nat.div_eq_of_lt hv, Nat.xor_zero]
  have hmod : ((a <<< 5) ^^^ v) % 2 ^ 5 = v := by
    rw [Nat.xor_mod_two_pow, Nat.shiftLeft_eq, Nat.mul_mod_left, Nat.mod_eq_of_lt hv,
      Nat.zero_xor]
  have := Nat.div_add_mod ((a <<< 5) ^^^ v) (2 ^ 5)
  rw [hdiv, hmod] at this
  have : (2 : Nat) ^ 5 = 32 := rfl
  omega

/-- Starting from a state `c`, the run over `l` is `T^[l.length] c` plus the run from 0. -/
theorem foldl_split (l : List Nat) (hl : ∀ v ∈ l, v < 32) (c : Nat) (hc : c < 2 ^ 30) :
    l.foldl Bech32.polymodStep c = T^[l.length] c ^^^ l.foldl Bech32.polymodStep 0 := by
  have h := foldl_xor l hl c 0 hc (by decide)
  rw [Nat.xor_zero] at h
  rw [← h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem eq_of_length_six (l : List Nat) (h : l.length = 6) :
    ∃ c₀ c₁ c₂ c₃ c₄ c₅, l = [c₀, c₁, c₂, c₃, c₄, c₅] := by
  rcases l with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, _ | ⟨c₄, _ | ⟨c₅, _ | ⟨c₆, l⟩⟩⟩⟩⟩⟩⟩
  all_goals simp at h
  exact ⟨_, _, _, _, _, _, rfl⟩

/-- Six 5-bit values run from 0 give their base-32 number, and every number below
    `2 ^ 30` is one. -/
theorem pack_iff (t : Nat) (ht : t < 2 ^ 30) (check : List Nat) :
    (check.length = 6 ∧ (∀ x ∈ check, x < 32) ∧ check.foldl Bech32.polymodStep 0 = t) ↔
    check = [(t >>> 25) % 32, (t >>> 20) % 32, (t >>> 15) % 32, (t >>> 10) % 32,
      (t >>> 5) % 32, (t >>> 0) % 32] := by
  have h30 : (2 : Nat) ^ 30 = 1073741824 := rfl
  simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
  constructor
  · rintro ⟨hlen, hlt, heq⟩
    obtain ⟨c₀, c₁, c₂, c₃, c₄, c₅, rfl⟩ := eq_of_length_six check hlen
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
    obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := hlt
    simp (disch := omega) only [List.foldl_cons, List.foldl_nil, polymodStep_small] at heq
    subst heq
    simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · intro h
    subst h
    refine ⟨rfl, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · simp (disch := omega) only [List.foldl_cons, List.foldl_nil, polymodStep_small]
      omega

theorem const_lt (v : Bech32.Variant) : v.const < 2 ^ 30 := by
  cases v <;> decide

theorem polymod_zeros (pre : List Nat) :
    Bech32.polymod (pre ++ [0, 0, 0, 0, 0, 0]) = T^[6] (Bech32.polymod pre) := by
  rw [polymod_append]
  rfl

theorem checksum_val (v : Bech32.Variant) (hrp : List Char) (vals : List Nat) :
    (Bech32.checksum v hrp vals).map Fin.val =
      let t := T^[6] (Bech32.polymod (Bech32.hrpExpand hrp ++ vals)) ^^^ v.const
      [(t >>> 25) % 32, (t >>> 20) % 32, (t >>> 15) % 32, (t >>> 10) % 32,
        (t >>> 5) % 32, (t >>> 0) % 32] := by
  simp only [checksum, polymod_zeros, List.map_cons, List.map_nil, Fin.val_ofNat]

/-- The six checksum values are determined: they are exactly what `checksum` writes. -/
theorem checksum_iff (v : Bech32.Variant) (hrp : List Char) (vals : List Nat)
    (hpre : ∀ x ∈ Bech32.hrpExpand hrp ++ vals, x < 32) (check : List Nat) :
    (check.length = 6 ∧ (∀ x ∈ check, x < 32) ∧
      Bech32.polymod (Bech32.hrpExpand hrp ++ vals ++ check) = v.const) ↔
    check = (Bech32.checksum v hrp vals).map Fin.val := by
  have hc := polymod_lt _ hpre
  have ht : T^[6] (Bech32.polymod (Bech32.hrpExpand hrp ++ vals)) ^^^ v.const < 2 ^ 30 :=
    Nat.xor_lt_two_pow (T_iterate_lt 6 _ hc) (const_lt v)
  rw [checksum_val, ← pack_iff _ ht]
  apply and_congr_right
  intro hlen
  apply and_congr_right
  intro hlt
  rw [polymod_append, foldl_split check hlt _ hc, hlen, xor_eq_iff]

/-! ### Inserting `q` before a final `p` -/

theorem polymod_snoc_one (a : List Nat) :
    Bech32.polymod (a ++ [1]) = T (Bech32.polymod a) ^^^ 1 := by
  rw [polymod_append, List.foldl_cons, List.foldl_nil, polymodStep_xor _ _ (by decide)]

theorem polymod_snoc_zero_one (a : List Nat) :
    Bech32.polymod (a ++ [0, 1]) = T (T (Bech32.polymod a)) ^^^ 1 := by
  rw [polymod_append, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    polymodStep_xor _ _ (by decide)]
  rfl

/-- The q insertion (value 0) before a final p (value 1). -/
theorem insert_bech32 (a : List Nat) (h : Bech32.polymod (a ++ [1]) = 1) :
    Bech32.polymod (a ++ [0, 1]) = 1 := by
  rw [polymod_snoc_one, Nat.xor_comm, xor_eq_iff, Nat.xor_self] at h
  rw [polymod_snoc_zero_one, h, T_zero, Nat.zero_xor]

theorem insert_bech32m (a : List Nat) (h : Bech32.polymod (a ++ [1]) = 0x2bc830a3) :
    Bech32.polymod (a ++ [0, 1]) ≠ 1 ∧ Bech32.polymod (a ++ [0, 1]) ≠ 0x2bc830a3 := by
  rw [polymod_snoc_one, Nat.xor_comm, xor_eq_iff] at h
  rw [polymod_snoc_zero_one, h]
  decide

end Bech32.Proofs
