import Research.Backfill.Paper6.ThmA
import Research.Backfill.Paper6.InclusionExclusion

/-!
# Sparse S0 witnesses: a recursive integer certificate with a semantic proof

Source candidate only; no development run or acceptance is claimed here.
The numerical recursion traverses a list of at most eight masks. It never
enumerates the 16384 points or a Finset of all subsets. The semantic proof uses
the accepted binary character and coordinate-product identities. Every resulting
witness is the actual frozen `polyOf (L.map RM714.maskSet)` polynomial.
-/

set_option autoImplicit false

namespace Paper6S0Witnesses

open BackfillPaper6.V3
open Paper6InclusionExclusion

/-- The character sum with the coordinates in `u` fixed to one. Integer
subtraction is intentional: no truncated-natural arithmetic is used. -/
def charCount : List ℕ → ℕ → ℤ
  | [], u => (2 : ℤ) ^ (14 - RM714.degNat u)
  | s :: L, u => charCount L u - 2 * charCount L (u ||| s)

theorem maskSet_lor (u s : ℕ) :
    RM714.maskSet (u ||| s) = RM714.maskSet u ∪ RM714.maskSet s := by
  ext i
  simp [RM714.maskSet]

theorem bit_monomial_union (u s : ℕ) (x : Pt 14) :
    (∏ j ∈ RM714.maskSet (u ||| s), bit (x j)) =
      (∏ j ∈ RM714.maskSet u, bit (x j)) *
        (∏ j ∈ RM714.maskSet s, bit (x j)) := by
  have hone : (∏ j ∈ RM714.maskSet (u ||| s), x j) = 1 ↔
      (∏ j ∈ RM714.maskSet u, x j) * (∏ j ∈ RM714.maskSet s, x j) = 1 := by
    rw [maskSet_lor, binary_mul_one_iff]
    simp only [binary_prod_one_iff, Finset.mem_union]
    constructor
    · intro h
      exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩
    · rintro ⟨hu, hs⟩ j (hj | hj)
      · exact hu j hj
      · exact hs j hj
  calc
    (∏ j ∈ RM714.maskSet (u ||| s), bit (x j)) =
        bit (∏ j ∈ RM714.maskSet (u ||| s), x j) :=
      (bit_prod _ x).symm
    _ = bit ((∏ j ∈ RM714.maskSet u, x j) *
        (∏ j ∈ RM714.maskSet s, x j)) := by simp only [bit, hone]
    _ = _ := by rw [bit_mul, bit_prod, bit_prod]

/-- This is the proof connecting the executable recursion to genuine evaluation
over the binary field. It applies to every list, including empty/repeated masks. -/
theorem charCount_eq_sum (L : List ℕ) (u : ℕ) :
    charCount L u = ∑ x : Pt 14,
      (∏ j ∈ RM714.maskSet u, bit (x j)) *
        character (RM714.evalPoly (L.map RM714.maskSet) x) := by
  induction L generalizing u with
  | nil =>
      simpa [charCount, RM714.evalPoly, character, bit, RM714.card_maskSet] using
        (sum_coordinate_product 14 (RM714.maskSet u)).symm
  | cons s L ih =>
      rw [charCount, ih, ih]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [List.map_cons, RM714.evalPoly, List.sum_cons, character_add]
      rw [bit_monomial_union]
      have hmono : character (∏ j ∈ RM714.maskSet s, x j) =
          1 + (-2) * (∏ j ∈ RM714.maskSet s, bit (x j)) := by
        rw [character, bit_prod]
      rw [hmono]
      ring

/-- The unrestricted character sum is `2^14 - 2*weight` of the actual polynomial. -/
theorem charCount_zero (L : List ℕ) :
    charCount L 0 = 16384 -
      2 * (hammingNorm (evalFun (polyOf (L.map RM714.maskSet))) : ℤ) := by
  have hz : RM714.maskSet 0 = ∅ := by ext i; simp [RM714.maskSet]
  rw [charCount_eq_sum, hz]
  simp only [Finset.prod_empty, one_mul]
  rw [Paper6ThmA.evalFun_polyOf_eq, weight_as_sum]
  simp only [character, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (Pt 14) = 16384 := by simp [Pt]
  rw [hcard]
  ring

/-- Data checked separately for each historical row. The mask bound is retained
for provenance even though the low-fourteen-bit interpretation already suffices. -/
def RowData (t : ℕ × List ℕ) : Prop :=
  (∀ s ∈ t.2, s < 16384) ∧
  (∀ s ∈ t.2, RM714.degNat s ≤ 7) ∧
  t.2.length ≤ 8 ∧ charCount t.2 0 = 16384 - 2 * (t.1 : ℤ)

instance rowDataDecidable (t : ℕ × List ℕ) : Decidable (RowData t) :=
  inferInstanceAs (Decidable
    ((∀ s ∈ t.2, s < 16384) ∧ (∀ s ∈ t.2, RM714.degNat s ≤ 7) ∧
      t.2.length ≤ 8 ∧ charCount t.2 0 = 16384 - 2 * (t.1 : ℤ)))

/-- Full sparse-polynomial conclusion, including both frozen bounds. -/
def SparseWeight (w : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin 14) (ZMod 2),
    p.totalDegree ≤ 7 ∧ p.support.card ≤ 8 ∧ hammingNorm (evalFun p) = w

theorem row_sound (t : ℕ × List ℕ) (h : RowData t) : SparseWeight t.1 := by
  refine ⟨polyOf (t.2.map RM714.maskSet), ?_, ?_, ?_⟩
  · apply Paper6ThmA.polyOf_degree_le
    intro S hS
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hS
    rw [RM714.card_maskSet]
    exact h.2.1 s hs
  · exact (Paper6ThmA.polyOf_support_card_le _).trans
      (by simpa only [List.length_map] using h.2.2.1)
  · have heq := charCount_zero t.2
    have hcert := h.2.2.2
    have hw : (hammingNorm (evalFun (polyOf (t.2.map RM714.maskSet))) : ℤ) =
        (t.1 : ℤ) := by linarith
    exact_mod_cast hw

/-- A small-membership presentation, proved equivalent to the frozen finite set.
The closed interval is not materialized as a 16065-element range during checking. -/
def normalizedS0 (w : ℕ) : Prop :=
  ((w ∈ K ∨ (w < 16065 ∧ 320 ≤ w ∧ w % 2 = 0)) ∨
    w ∈ K.image (fun k => 16384 - k)) ∧ w ∉ U

instance normalizedS0Decidable (w : ℕ) : Decidable (normalizedS0 w) :=
  inferInstanceAs (Decidable
    (((w ∈ K ∨ (w < 16065 ∧ 320 ≤ w ∧ w % 2 = 0)) ∨
      w ∈ K.image (fun k => 16384 - k)) ∧ w ∉ U))

theorem mem_S0_iff (w : ℕ) : w ∈ S0 ↔ normalizedS0 w := by
  simp only [S0, normalizedS0, Finset.mem_sdiff, Finset.mem_union,
    Finset.mem_filter, Finset.mem_range, Nat.even_iff]

theorem normalizedS0_bound (w : ℕ) (hw : normalizedS0 w) : w < 16385 := by
  rcases hw.1 with (hK | hI) | hC
  · have hsmall : ∀ k ∈ K, k < 16385 := by decide +kernel
    exact hsmall w hK
  · omega
  · obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hC
    omega

/-- One numerical shard contains 256 consecutive possible weights. -/
def BlockResult (b : ℕ) : Prop :=
  ∀ i : Fin 256, normalizedS0 (256 * b + i.val) →
    SparseWeight (256 * b + i.val)

theorem block_sound (b : ℕ) (rows : List (ℕ × List ℕ))
    (hrows : ∀ t ∈ rows, RowData t)
    (hcover : ∀ i : Fin 256, normalizedS0 (256 * b + i.val) →
      256 * b + i.val ∈ rows.map Prod.fst) : BlockResult b := by
  intro i hi
  obtain ⟨t, ht, hweight⟩ := List.mem_map.mp (hcover i hi)
  rw [← hweight]
  exact row_sound t (hrows t ht)

end Paper6S0Witnesses

#print axioms Paper6S0Witnesses.charCount
#print axioms Paper6S0Witnesses.maskSet_lor
#print axioms Paper6S0Witnesses.bit_monomial_union
#print axioms Paper6S0Witnesses.charCount_eq_sum
#print axioms Paper6S0Witnesses.charCount_zero
#print axioms Paper6S0Witnesses.RowData
#print axioms Paper6S0Witnesses.rowDataDecidable
#print axioms Paper6S0Witnesses.SparseWeight
#print axioms Paper6S0Witnesses.row_sound
#print axioms Paper6S0Witnesses.normalizedS0
#print axioms Paper6S0Witnesses.normalizedS0Decidable
#print axioms Paper6S0Witnesses.mem_S0_iff
#print axioms Paper6S0Witnesses.normalizedS0_bound
#print axioms Paper6S0Witnesses.BlockResult
#print axioms Paper6S0Witnesses.block_sound
