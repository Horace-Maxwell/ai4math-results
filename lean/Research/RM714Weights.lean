import Mathlib

/-!
# Weights of the binary Reed–Muller code RM(7,14): explicit codewords

A codeword of the binary Reed–Muller code `RM(7,14)` is the truth table on `𝔽₂¹⁴` of a polynomial
over `𝔽₂ = ZMod 2` in 14 variables of total degree `≤ 7`.  A polynomial is given by the list of its
monomials; a monomial is given by its set of variables `S ⊆ Fin 14` and stands for `∏_{i ∈ S} x i`.

`IsRM714Weight w` says: some polynomial all of whose monomials have degree `≤ 7` takes the value `1`
at exactly `w` points of `𝔽₂¹⁴`, i.e. `w` is a weight of `RM(7,14)`.

The weights of the explicit witnesses are computed on 14-bit numbers by `decide +kernel`.
The bridge `weight_map_maskSet` proves, for every list of monomials, that this bit computation
equals the weight defined above (via Mathlib's `finFunctionFinEquiv`).
-/

set_option autoImplicit false

open Finset

namespace RM714

/-- The value at `x ∈ 𝔽₂¹⁴` of the polynomial `∑_{S ∈ L} ∏_{i ∈ S} x i` over `𝔽₂`. -/
def evalPoly (L : List (Finset (Fin 14))) (x : Fin 14 → ZMod 2) : ZMod 2 :=
  (L.map fun S => ∏ i ∈ S, x i).sum

/-- Hamming weight of the truth table of `evalPoly L`. -/
def weight (L : List (Finset (Fin 14))) : ℕ :=
  #{x : Fin 14 → ZMod 2 | evalPoly L x = 1}

/-- `w` is a weight of the Reed–Muller code `RM(7,14)`. -/
def IsRM714Weight (w : ℕ) : Prop :=
  ∃ L : List (Finset (Fin 14)), (∀ S ∈ L, S.card ≤ 7) ∧ weight L = w

/-! ### Bit-mask computation -/

/-- The monomial with variable mask `s`, evaluated at the point with bit pattern `a`. -/
def monoVal (s a : ℕ) : Bool := Nat.beq (a &&& s) s

/-- The polynomial with monomial masks `L`, evaluated at the point with bit pattern `a`. -/
def polyVal (L : List ℕ) (a : ℕ) : Bool := L.foldr (fun s b => xor (monoVal s a) b) false

/-- Weight computed on bit patterns `a < 2 ^ 14` (a list count, cheap for the kernel). -/
def weightNat (L : List ℕ) : ℕ := (List.range (2 ^ 14)).countP fun a => polyVal L a

/-- The set of variables of the monomial with mask `s`. -/
def maskSet (s : ℕ) : Finset (Fin 14) := {i | s.testBit i = true}

/-- Points of `𝔽₂¹⁴` as 14-bit numbers (coordinate `i` is bit `i`). -/
def pointEquiv : (Fin 14 → ZMod 2) ≃ Fin (2 ^ 14) := finFunctionFinEquiv

lemma testBit_pointEquiv (x : Fin 14 → ZMod 2) (i : Fin 14) :
    (pointEquiv x : ℕ).testBit i = decide (x i = 1) := by
  have h := finFunctionFinEquiv_symm_apply_val (m := 2) (n := 14) (pointEquiv x) i
  have hx : (finFunctionFinEquiv (m := 2) (n := 14)).symm (pointEquiv x) = x :=
    Equiv.symm_apply_apply _ x
  rw [hx] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, ← h]
  have key : ∀ z : Fin 2, ((z : ℕ) = 1 ↔ z = 1) := by decide
  exact decide_eq_decide.mpr (key (x i))

lemma monoVal_iff (s a : ℕ) (hs : s < 2 ^ 14) :
    monoVal s a = true ↔ ∀ i : Fin 14, s.testBit i = true → a.testBit i = true := by
  unfold monoVal
  constructor
  · intro h i hi
    have he : a &&& s = s := Nat.eq_of_beq_eq_true h
    have := congrArg (fun n => n.testBit i) he
    simp only [Nat.testBit_land, hi, Bool.and_true] at this
    exact this
  · intro h
    have he : a &&& s = s := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_land]
      by_cases hj : j < 14
      · have hji := h ⟨j, hj⟩
        cases hsj : s.testBit j
        · simp
        · simp only [hsj] at hji ⊢
          simp [hji trivial]
      · have hlt : s < 2 ^ j :=
          lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) (by omega))
        have : s.testBit j = false := Nat.testBit_eq_false_of_lt hlt
        simp [this]
    rw [he]
    exact Nat.beq_refl s

lemma prod_maskSet (x : Fin 14 → ZMod 2) (s : ℕ) (hs : s < 2 ^ 14) :
    ∏ i ∈ maskSet s, x i = if monoVal s (pointEquiv x : ℕ) then 1 else 0 := by
  by_cases h : monoVal s (pointEquiv x : ℕ) = true
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    have hsi : s.testBit i = true := by simpa [maskSet] using hi
    have := (monoVal_iff s _ hs).1 h i hsi
    rw [testBit_pointEquiv] at this
    simpa using this
  · rw [if_neg h]
    obtain ⟨i, hsi, hai⟩ : ∃ i : Fin 14, s.testBit i = true ∧ ¬ (pointEquiv x : ℕ).testBit i = true := by
      by_contra hc
      push Not at hc
      exact h ((monoVal_iff s _ hs).2 hc)
    apply Finset.prod_eq_zero (i := i)
    · simp [maskSet, hsi]
    · rw [testBit_pointEquiv] at hai
      have hne : x i ≠ 1 := by simpa using hai
      have key : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide
      exact key (x i) hne

lemma evalPoly_map_maskSet (L : List ℕ) (hL : ∀ s ∈ L, s < 2 ^ 14) (x : Fin 14 → ZMod 2) :
    evalPoly (L.map maskSet) x = if polyVal L (pointEquiv x : ℕ) then 1 else 0 := by
  induction L with
  | nil => simp [evalPoly, polyVal]
  | cons s L ih =>
    have ih' := ih (fun t ht => hL t (List.mem_cons_of_mem s ht))
    unfold evalPoly at ih' ⊢
    rw [List.map_cons, List.map_cons, List.sum_cons, ih', prod_maskSet x s (hL s List.mem_cons_self)]
    show _ = if xor (monoVal s (pointEquiv x : ℕ)) (polyVal L (pointEquiv x : ℕ)) then 1 else 0
    cases monoVal s (pointEquiv x : ℕ) <;> cases polyVal L (pointEquiv x : ℕ) <;> decide

/-- Counting over `Fin n` is counting over `List.range n`. -/
lemma card_fin_filter_eq_countP (n : ℕ) (p : ℕ → Bool) :
    #{a : Fin n | p a.val = true} = (List.range n).countP p := by
  have h1 : (({a : Fin n | p a.val = true} : Finset (Fin n))).map Fin.valEmbedding
      = {k ∈ Finset.range n | p k = true} := by
    rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, Finset.filter_map]
    rfl
  rw [← Finset.card_map Fin.valEmbedding, h1, Finset.card_def, Finset.filter_val,
    Finset.range_val, ← Multiset.countP_eq_card_filter]
  show Multiset.countP _ (↑(List.range n) : Multiset ℕ) = _
  rw [Multiset.coe_countP]
  simp

/-- Bridge: the bit computation `weightNat` is the Hamming weight of the polynomial. -/
theorem weight_map_maskSet (L : List ℕ) (hL : ∀ s ∈ L, s < 2 ^ 14) :
    weight (L.map maskSet) = weightNat L := by
  have h : weight (L.map maskSet) = #{a : Fin (2 ^ 14) | polyVal L a.val = true} := by
    unfold weight
    apply Finset.card_equiv pointEquiv
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [evalPoly_map_maskSet L hL x]
    cases polyVal L (pointEquiv x : ℕ) <;> decide
  rw [h, card_fin_filter_eq_countP]
  rfl

/-- Number of variables of the monomial with mask `s` (its degree), computed on `ℕ`. -/
def degNat (s : ℕ) : ℕ := (List.range 14).countP fun i => s.testBit i

lemma card_maskSet (s : ℕ) : (maskSet s).card = degNat s := by
  unfold maskSet degNat
  exact card_fin_filter_eq_countP 14 (fun i => s.testBit i)

/-- A monomial list with masks `< 2 ^ 14`, all of degree `≤ 7`, whose bit-computed weight is `w`,
certifies that `w` is a weight of `RM(7,14)`. -/
theorem isRM714Weight_of (L : List ℕ) (w : ℕ) (hL : ∀ s ∈ L, s < 2 ^ 14)
    (hdeg : L.all (fun s => decide (degNat s ≤ 7)) = true) (hw : weightNat L = w) :
    IsRM714Weight w := by
  refine ⟨L.map maskSet, ?_, ?_⟩
  · intro S hS
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hS
    have := List.all_eq_true.1 hdeg s hs
    rw [card_maskSet]
    simpa using this
  · rw [weight_map_maskSet L hL, hw]

/-! ### Witnesses (monomials as 14-bit masks; bit `i` = variable `x_{i+1}`) -/

/-- `x1x2x3x4x5x6x7 + x1x2x3x5x6x7x11 + x1x3x6x7x10x12x13 + x3x4x6x7x10x12x13 + x8x9x10x11x12x13x14` -/
def L354 : List ℕ := [127,  1143,  6757,  6764,  16256]

theorem isRM714Weight_354 : IsRM714Weight 354 :=
  isRM714Weight_of L354 354 (by decide) (by decide +kernel) (by decide +kernel)

/-- `1 + x1x2x3x4x5x6x7 + x1x2x3x5x6x7x11 + x1x3x6x7x10x12x13 + x3x4x6x7x10x12x13 + x8x9x10x11x12x13x14` -/
def L16030 : List ℕ := [0,  127,  1143,  6757,  6764,  16256]

theorem isRM714Weight_16030 : IsRM714Weight 16030 :=
  isRM714Weight_of L16030 16030 (by decide) (by decide +kernel) (by decide +kernel)

/-- `x3x4x6 + x1x2x3x4x5x6x7 + x1x5x7x11x13 + x6x14 + x8x9x10x11x12x13x14` -/
def L4378 : List ℕ := [44,  127,  5201,  8224,  16256]

theorem isRM714Weight_4378 : IsRM714Weight 4378 :=
  isRM714Weight_of L4378 4378 (by decide) (by decide +kernel) (by decide +kernel)

/-- `x2x6x7x9x12 + x3x4x5x8x9x10x13 + x8x14 + x1x3x5x9x10x11x14` -/
def L4380 : List ℕ := [2402,  5020,  8320,  10005]

theorem isRM714Weight_4380 : IsRM714Weight 4380 :=
  isRM714Weight_of L4380 4380 (by decide) (by decide +kernel) (by decide +kernel)

/-- `x1x2x5x6x7 + x1x2x3x4x5x6x7 + x4x9 + x3x4x6x8x12 + x8x9x10x11x12x13x14` -/
def L4382 : List ℕ := [115,  127,  264,  2220,  16256]

theorem isRM714Weight_4382 : IsRM714Weight 4382 :=
  isRM714Weight_of L4382 4382 (by decide) (by decide +kernel) (by decide +kernel)

/-- `x7 + x1x2x3x4x5x6x7 + x5x10 + x2x3x4x5x8x10x11 + x1x2x4x6x13x14 + x8x9x10x11x12x13x14` -/
def L8174 : List ℕ := [64,  127,  528,  1694,  12331,  16256]

theorem isRM714Weight_8174 : IsRM714Weight 8174 :=
  isRM714Weight_of L8174 8174 (by decide) (by decide +kernel) (by decide +kernel)

/-- `x7 + x1x2x3x4x5x6x7 + x2x5x6x13 + x2x5x8x10x13x14 + x8x9x10x11x12x13x14` -/
def L8178 : List ℕ := [64,  127,  4146,  12946,  16256]

theorem isRM714Weight_8178 : IsRM714Weight 8178 :=
  isRM714Weight_of L8178 8178 (by decide) (by decide +kernel) (by decide +kernel)

/-- `x1x2x3x4x5x6x7 + x8 + x1x2x3x4x6x11x13 + x1x14 + x2x7x8x10x11x12x14 + x8x9x10x11x12x13x14` -/
def L8182 : List ℕ := [127,  128,  5167,  8193,  11970,  16256]

theorem isRM714Weight_8182 : IsRM714Weight 8182 :=
  isRM714Weight_of L8182 8182 (by decide) (by decide +kernel) (by decide +kernel)

/-- `x1x2x3x4x5x6x7 + x11 + x4x12 + x1x2x8x10x11x12x13 + x8x9x10x11x12x13x14` -/
def L8186 : List ℕ := [127,  1024,  2056,  7811,  16256]

theorem isRM714Weight_8186 : IsRM714Weight 8186 :=
  isRM714Weight_of L8186 8186 (by decide) (by decide +kernel) (by decide +kernel)

/-- `x1 + x2x5x6x8x9x10x13 + x2x14 + x1x4x6x7x11x12x14` -/
def L8188 : List ℕ := [1,  5042,  8194,  11369]

theorem isRM714Weight_8188 : IsRM714Weight 8188 :=
  isRM714Weight_of L8188 8188 (by decide) (by decide +kernel) (by decide +kernel)

/-- `x2 + x1x2x3x4x5x6x7 + x1x7x8 + x8x9x10x11x12x13x14` -/
def L8190 : List ℕ := [2,  127,  193,  16256]

theorem isRM714Weight_8190 : IsRM714Weight 8190 :=
  isRM714Weight_of L8190 8190 (by decide) (by decide +kernel) (by decide +kernel)

/-- `1 + x2 + x1x2x3x4x5x6x7 + x1x7x8 + x8x9x10x11x12x13x14` -/
def L8194 : List ℕ := [0,  2,  127,  193,  16256]

theorem isRM714Weight_8194 : IsRM714Weight 8194 :=
  isRM714Weight_of L8194 8194 (by decide) (by decide +kernel) (by decide +kernel)

/-- `1 + x1 + x2x5x6x8x9x10x13 + x2x14 + x1x4x6x7x11x12x14` -/
def L8196 : List ℕ := [0,  1,  5042,  8194,  11369]

theorem isRM714Weight_8196 : IsRM714Weight 8196 :=
  isRM714Weight_of L8196 8196 (by decide) (by decide +kernel) (by decide +kernel)

/-- `1 + x1x2x3x4x5x6x7 + x11 + x4x12 + x1x2x8x10x11x12x13 + x8x9x10x11x12x13x14` -/
def L8198 : List ℕ := [0,  127,  1024,  2056,  7811,  16256]

theorem isRM714Weight_8198 : IsRM714Weight 8198 :=
  isRM714Weight_of L8198 8198 (by decide) (by decide +kernel) (by decide +kernel)

/-- `1 + x1x2x3x4x5x6x7 + x8 + x1x2x3x4x6x11x13 + x1x14 + x2x7x8x10x11x12x14 + x8x9x10x11x12x13x14` -/
def L8202 : List ℕ := [0,  127,  128,  5167,  8193,  11970,  16256]

theorem isRM714Weight_8202 : IsRM714Weight 8202 :=
  isRM714Weight_of L8202 8202 (by decide) (by decide +kernel) (by decide +kernel)

/-- `1 + x7 + x1x2x3x4x5x6x7 + x2x5x6x13 + x2x5x8x10x13x14 + x8x9x10x11x12x13x14` -/
def L8206 : List ℕ := [0,  64,  127,  4146,  12946,  16256]

theorem isRM714Weight_8206 : IsRM714Weight 8206 :=
  isRM714Weight_of L8206 8206 (by decide) (by decide +kernel) (by decide +kernel)

/-- `1 + x7 + x1x2x3x4x5x6x7 + x5x10 + x2x3x4x5x8x10x11 + x1x2x4x6x13x14 + x8x9x10x11x12x13x14` -/
def L8210 : List ℕ := [0,  64,  127,  528,  1694,  12331,  16256]

theorem isRM714Weight_8210 : IsRM714Weight 8210 :=
  isRM714Weight_of L8210 8210 (by decide) (by decide +kernel) (by decide +kernel)

/-- The 14 weights of the list `M` of arXiv:2606.21425v1 (Prop. 4) that we settle, and the three
auxiliary weights 4378, 4380, 4382 of its final Remark, are weights of `RM(7,14)`. -/
theorem rm714_new_weights :
    ∀ w ∈ ([354,  16030,  4378,  4380,  4382,  8174,  8178,  8182,  8186,  8188,  8190,  8194,  8196,  8198,  8202,  8206,  8210] : List ℕ), IsRM714Weight w := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact isRM714Weight_354
  · exact isRM714Weight_16030
  · exact isRM714Weight_4378
  · exact isRM714Weight_4380
  · exact isRM714Weight_4382
  · exact isRM714Weight_8174
  · exact isRM714Weight_8178
  · exact isRM714Weight_8182
  · exact isRM714Weight_8186
  · exact isRM714Weight_8188
  · exact isRM714Weight_8190
  · exact isRM714Weight_8194
  · exact isRM714Weight_8196
  · exact isRM714Weight_8198
  · exact isRM714Weight_8202
  · exact isRM714Weight_8206
  · exact isRM714Weight_8210

end RM714

#print axioms RM714.rm714_new_weights
#print axioms RM714.weight_map_maskSet
