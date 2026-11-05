import Research.Backfill.Paper7.IntroIntegralDegreeTwoChain
import Research.Backfill.Paper7.IntroFourRootLeafExclusion

/-! Exact leaf moments from the two actual neighborhood rows of one
subdivided pendant arm. No moment identity is an input hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroAttachmentMoments
open Matrix SimpleGraph Paper7IntroLocalQuartic Paper7IntroFourExternal

theorem subdivided_arm_square_column
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a y l : V)
    (hal : a ≠ l)
    (hy : ∀ z, G.Adj y z ↔ z = a ∨ z = l)
    (hl : ∀ z, G.Adj l z ↔ z = y) :
    (G.adjMatrix ℝ) ^ 2 *ᵥ Pi.single l 1 = Pi.single a 1 + Pi.single l 1 := by
  rw [pow_two, ← Matrix.mulVec_mulVec, adjacency_single_one G l y hl]
  exact adjacency_single_of_two_neighbors G y a l hal hy
#print axioms Paper7IntroAttachmentMoments.subdivided_arm_square_column

theorem subdivided_arm_leaf_even_moments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a y l : V)
    (hal : a ≠ l)
    (hy : ∀ z, G.Adj y z ↔ z = a ∨ z = l)
    (hl : ∀ z, G.Adj l z ↔ z = y) :
    ((G.adjMatrix ℝ) ^ 2) l l = 1 ∧
      ((G.adjMatrix ℝ) ^ 4) l l = 2 ∧
      ((G.adjMatrix ℝ) ^ 6) l l = (G.degree a : ℝ) + 3 := by
  let A := G.adjMatrix ℝ
  have hA : A.IsSymm := G.isSymm_adjMatrix
  have h1 : A *ᵥ Pi.single l 1 = Pi.single y 1 := adjacency_single_one G l y hl
  have h2 : A ^ 2 *ᵥ Pi.single l 1 = Pi.single a 1 + Pi.single l 1 :=
    subdivided_arm_square_column G a y l hal hy hl
  have h3 : A ^ 3 *ᵥ Pi.single l 1 = A *ᵥ Pi.single a 1 + Pi.single y 1 := by
    rw [pow_succ', ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_add, h1]
  have hm2 : (A ^ 2) l l = 1 := by
    rw [symmetric_square_diagonal A hA l, h1]
    simp only [single_dotProduct, one_mul, Pi.single_eq_same]
  have hm4 : (A ^ 4) l l = 2 := by
    rw [show A ^ 4 = (A ^ 2) ^ 2 from pow_mul A 2 2,
      symmetric_square_diagonal (A ^ 2) (hA.pow 2) l, h2]
    simp only [add_dotProduct, dotProduct_add, single_dotProduct, one_mul,
      Pi.single_eq_same, Pi.single_eq_of_ne hal, Pi.single_eq_of_ne hal.symm]
    norm_num
  have hnorm : (A *ᵥ Pi.single a 1) ⬝ᵥ (A *ᵥ Pi.single a 1) =
      (G.degree a : ℝ) := by
    rw [← symmetric_square_diagonal A hA a]
    change ((G.adjMatrix ℝ) ^ 2) a a = _
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have hya : (A *ᵥ Pi.single a 1) y = 1 := by
    rw [Matrix.mulVec_single_one]
    exact ite_eq_left ((hy a).mpr (Or.inl rfl))
  have hm6 : (A ^ 6) l l = (G.degree a : ℝ) + 3 := by
    rw [show A ^ 6 = (A ^ 3) ^ 2 from pow_mul A 3 2,
      symmetric_square_diagonal (A ^ 3) (hA.pow 3) l, h3]
    simp only [add_dotProduct, dotProduct_add, dotProduct_single, mul_one,
      single_dotProduct, Pi.add_apply, Pi.single_eq_same, hnorm, hya]
    ring
  exact ⟨hm2, hm4, hm6⟩
#print axioms Paper7IntroAttachmentMoments.subdivided_arm_leaf_even_moments

theorem subdivided_arm_leaf_sixth_gap
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a y l : V)
    (hal : a ≠ l)
    (hy : ∀ z, G.Adj y z ↔ z = a ∨ z = l)
    (hl : ∀ z, G.Adj l z ↔ z = y) :
    ((G.adjMatrix ℝ) ^ 6 - (5 : ℝ) • (G.adjMatrix ℝ) ^ 4 +
      (4 : ℝ) • (G.adjMatrix ℝ) ^ 2) l l = (G.degree a : ℝ) - 3 := by
  obtain ⟨hm2, hm4, hm6⟩ := subdivided_arm_leaf_even_moments G a y l hal hy hl
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    hm2, hm4, hm6]
  ring
#print axioms Paper7IntroAttachmentMoments.subdivided_arm_leaf_sixth_gap

end Paper7IntroAttachmentMoments
