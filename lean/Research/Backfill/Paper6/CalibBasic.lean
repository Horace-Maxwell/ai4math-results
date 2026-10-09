import Research.Backfill.Paper6.ChallengeV3
import Research.Backfill.Paper6.ThmA

/-!
# Calibration witnesses: twelve-variable semantic and blocked-count bridges

Candidate proof source, not yet compiled or accepted. The fixed-dimension bit bridge
is adapted from the already existing RM714Weights source by replacing dimension 14
with 12; every proof is present below. The generic polynomial degree lemma is imported
from Paper6ThmA.polyOf_degree_le, with its exact source hash recorded in MANIFEST.json.
No unproved old Challenge proposition is used as a hypothesis or axiom.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

open Finset
open BackfillPaper6.V3

/-- The value at `x ∈ 𝔽₂¹²` of the polynomial `∑_{S ∈ L} ∏_{i ∈ S} x i` over `𝔽₂`. -/
def evalPoly (L : List (Finset (Fin 12))) (x : Fin 12 → ZMod 2) : ZMod 2 :=
  (L.map fun S => ∏ i ∈ S, x i).sum

/-- Hamming weight of the truth table of `evalPoly L`. -/
def weight (L : List (Finset (Fin 12))) : ℕ :=
  #{x : Fin 12 → ZMod 2 | evalPoly L x = 1}

/-! ### Bit-mask computation -/

/-- The monomial with variable mask `s`, evaluated at the point with bit pattern `a`. -/
def monoVal (s a : ℕ) : Bool := Nat.beq (a &&& s) s

/-- The polynomial with monomial masks `L`, evaluated at the point with bit pattern `a`. -/
def polyVal (L : List ℕ) (a : ℕ) : Bool := L.foldr (fun s b => xor (monoVal s a) b) false

/-- Weight computed on bit patterns `a < 2 ^ 12` (a list count, cheap for the kernel). -/
def weightNat (L : List ℕ) : ℕ := (List.range (2 ^ 12)).countP fun a => polyVal L a

/-- The set of variables of the monomial with mask `s`. -/
def maskSet (s : ℕ) : Finset (Fin 12) := {i | s.testBit i = true}

/-- Points of `𝔽₂¹²` as 12-bit numbers (coordinate `i` is bit `i`). -/
def pointEquiv : (Fin 12 → ZMod 2) ≃ Fin (2 ^ 12) := finFunctionFinEquiv

lemma testBit_pointEquiv (x : Fin 12 → ZMod 2) (i : Fin 12) :
    (pointEquiv x : ℕ).testBit i = decide (x i = 1) := by
  have h := finFunctionFinEquiv_symm_apply_val (m := 2) (n := 12) (pointEquiv x) i
  have hx : (finFunctionFinEquiv (m := 2) (n := 12)).symm (pointEquiv x) = x :=
    Equiv.symm_apply_apply _ x
  rw [hx] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, ← h]
  have key : ∀ z : Fin 2, ((z : ℕ) = 1 ↔ z = 1) := by decide
  exact decide_eq_decide.mpr (key (x i))

lemma monoVal_iff (s a : ℕ) (hs : s < 2 ^ 12) :
    monoVal s a = true ↔ ∀ i : Fin 12, s.testBit i = true → a.testBit i = true := by
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
      by_cases hj : j < 12
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

lemma prod_maskSet (x : Fin 12 → ZMod 2) (s : ℕ) (hs : s < 2 ^ 12) :
    ∏ i ∈ maskSet s, x i = if monoVal s (pointEquiv x : ℕ) then 1 else 0 := by
  by_cases h : monoVal s (pointEquiv x : ℕ) = true
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i hi
    have hsi : s.testBit i = true := by simpa [maskSet] using hi
    have := (monoVal_iff s _ hs).1 h i hsi
    rw [testBit_pointEquiv] at this
    simpa using this
  · rw [ite_eq_right h]
    obtain ⟨i, hsi, hai⟩ : ∃ i : Fin 12, s.testBit i = true ∧ ¬ (pointEquiv x : ℕ).testBit i = true := by
      by_contra hc
      push Not at hc
      exact h ((monoVal_iff s _ hs).2 hc)
    apply Finset.prod_eq_zero (i := i)
    · simp [maskSet, hsi]
    · rw [testBit_pointEquiv] at hai
      have hne : x i ≠ 1 := by simpa using hai
      have key : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide
      exact key (x i) hne

lemma evalPoly_map_maskSet (L : List ℕ) (hL : ∀ s ∈ L, s < 2 ^ 12) (x : Fin 12 → ZMod 2) :
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
theorem weight_map_maskSet (L : List ℕ) (hL : ∀ s ∈ L, s < 2 ^ 12) :
    weight (L.map maskSet) = weightNat L := by
  have h : weight (L.map maskSet) = #{a : Fin (2 ^ 12) | polyVal L a.val = true} := by
    unfold weight
    apply Finset.card_equiv pointEquiv
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [evalPoly_map_maskSet L hL x]
    cases polyVal L (pointEquiv x : ℕ) <;> decide
  rw [h, card_fin_filter_eq_countP]
  rfl

/-- Number of variables of the monomial with mask `s` (its degree), computed on `ℕ`. -/
def degNat (s : ℕ) : ℕ := (List.range 12).countP fun i => s.testBit i

lemma card_maskSet (s : ℕ) : (maskSet s).card = degNat s := by
  unfold maskSet degNat
  exact card_fin_filter_eq_countP 12 (fun i => s.testBit i)

/-- The polynomial list encoding and the old list evaluation agree pointwise. -/
theorem evalFun_polyOf_eq (L : List (Finset (Fin 12))) :
    evalFun (polyOf L) = evalPoly L := by
  funext x
  simp only [evalFun, polyOf, evalPoly, map_list_sum,
    List.map_map, Function.comp_def,
    MvPolynomial.eval_prod, MvPolynomial.eval_X]

/-- Over the binary field, counting nonzero values is counting values equal to one. -/
theorem hammingNorm_polyOf_eq_weight
    (L : List (Finset (Fin 12))) :
    hammingNorm (evalFun (polyOf L)) = weight L := by
  classical
  have hz : ∀ z : ZMod 2, z ≠ 0 ↔ z = 1 := by decide
  rw [evalFun_polyOf_eq]
  unfold hammingNorm weight
  congr 1
  exact Finset.filter_congr (fun x _ => hz _)


/-- Counts a prefix without prescribing how the concrete computation is split. -/
def countPrefix (L : List ℕ) (n : ℕ) : ℕ :=
  (List.range n).countP (polyVal L)

/-- A block of exactly 64 evaluation points beginning at `a`. -/
def blockCount (L : List ℕ) (a : ℕ) : ℕ :=
  (List.range 64).countP (fun i => polyVal L (a + i))

/-- The assembly step is a generic list identity, not a trusted numeric oracle. -/
theorem prefix_step (L : List ℕ) (a : ℕ) :
    countPrefix L (a + 64) = countPrefix L a + blockCount L a := by
  simp only [countPrefix, blockCount, List.range_add, List.countP_append,
    List.countP_map, Function.comp_def]

/-- All hypotheses are directly checked from the concrete mask data and block counts. -/
theorem concrete_witness (L : List ℕ) (w : ℕ)
    (hmask : ∀ s ∈ L, s < 2 ^ 12)
    (hdeg : L.all (fun s => decide (degNat s ≤ 6)) = true)
    (hw : countPrefix L 4096 = w) : BackfillPaper6.V3.IsWeight 6 12 w := by
  refine ⟨evalFun (polyOf (L.map maskSet)), ⟨polyOf (L.map maskSet), ?_, rfl⟩, ?_⟩
  · apply Paper6ThmA.polyOf_degree_le
    intro S hS
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hS
    have hd := List.all_eq_true.mp hdeg s hs
    rw [card_maskSet]
    simpa using hd
  · rw [hammingNorm_polyOf_eq_weight, weight_map_maskSet L hmask]
    change weightNat L = w at hw
    exact hw

end Paper6Calib

#print axioms Paper6Calib.testBit_pointEquiv
#print axioms Paper6Calib.monoVal_iff
#print axioms Paper6Calib.prod_maskSet
#print axioms Paper6Calib.evalPoly_map_maskSet
#print axioms Paper6Calib.card_fin_filter_eq_countP
#print axioms Paper6Calib.weight_map_maskSet
#print axioms Paper6Calib.card_maskSet
#print axioms Paper6Calib.evalFun_polyOf_eq
#print axioms Paper6Calib.hammingNorm_polyOf_eq_weight
#print axioms Paper6Calib.prefix_step
#print axioms Paper6Calib.concrete_witness
