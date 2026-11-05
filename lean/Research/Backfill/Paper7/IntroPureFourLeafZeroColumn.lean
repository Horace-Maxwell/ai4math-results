import Research.Backfill.Paper7.IntroRadiusThreeFourProjector
import Research.Backfill.Paper7.IntroPureLeafSumEvenMoments
import Research.Backfill.Paper7.IntroPureLeafStarCycleFourthConstraint

/-! Exact whole-leaf moments in the four-leaf, degree-six branch force
the actual Q0 and P4 columns at c to vanish. Neither kernel relation nor
any numerical moment is an input assumption. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroFourLeafColumn
open Matrix SimpleGraph BackfillPaper7.Challenge
open Paper7IntroFourProjector Paper7IntroZeroOneProjectors Paper7IntroPureLeafMoments
open Paper7IntroPureLeafConstraints Paper7IntroAttachmentMoments

theorem pure_four_leaf_degree_six_zero_columns
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3) (a c : V)
    (Y : Finset V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a)
    (l : V) (hl : l ∈ Y) (hm : Y.card = 4) (hd : G.degree c = 6) :
    radiusThreeQ0 (G.adjMatrix ℝ) *ᵥ Pi.single c 1 = 0 ∧
      ((G.adjMatrix ℝ) ^ 6) c c = 456 ∧
      radiusThreeP4 (G.adjMatrix ℝ) *ᵥ Pi.single c 1 = 0 := by
  let A := G.adjMatrix ℝ
  let L : V → ℝ := ∑ y ∈ Y, Pi.single y 1
  have hA : A.IsSymm := G.isSymm_adjMatrix
  obtain ⟨hL0, _hAL, hL2, hL4, hL6⟩ :=
    pure_leaf_star_leaf_sum_even_moments G a c Y hc hNa hNl
  change L ⬝ᵥ L = (Y.card : ℝ) at hL0
  change L ⬝ᵥ A ^ 2 *ᵥ L = (Y.card : ℝ) ^ 2 at hL2
  change L ⬝ᵥ A ^ 4 *ᵥ L = (Y.card : ℝ) ^ 2 * ((Y.card : ℝ) + 1) at hL4
  change L ⬝ᵥ A ^ 6 *ᵥ L = (Y.card : ℝ) ^ 2 *
    ((Y.card : ℝ) ^ 2 + 2 * (Y.card : ℝ) + (G.degree c : ℝ)) at hL6
  rw [hm] at hL0 hL2 hL4 hL6
  rw [hd] at hL6
  norm_num at hL0 hL2 hL4 hL6
  have hQval : L ⬝ᵥ radiusThreeQ0 A *ᵥ L = 0 := by
    simp only [radiusThreeQ0, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul,
      smul_eq_mul, hL0, hL2, hL4, hL6]
    norm_num
  obtain ⟨hQA, hQsq, _hP1sq⟩ := integral_radius_three_Q0_P1_relations G hI hbound
  have hQsym : (radiusThreeQ0 A).IsSymm :=
    (((Matrix.isSymm_one.smul (36 : ℝ)).sub ((hA.pow 2).smul 49)).add
      ((hA.pow 4).smul 14)).sub (hA.pow 6)
  have hQL := symmetric_scaled_idempotent_quadratic_zero
    (radiusThreeQ0 A) hQsym 36 hQsq L hQval
  have hAa : A *ᵥ Pi.single a 1 = Pi.single c 1 + L := by
    change G.adjMatrix ℝ *ᵥ Pi.single a 1 = Pi.single c 1 + ∑ y ∈ Y, Pi.single y 1
    rw [adjacency_single_finset G a (insert c Y) hNa, Finset.sum_insert hc]
  have hQc : radiusThreeQ0 A *ᵥ Pi.single c 1 = 0 := by
    have hz : radiusThreeQ0 A *ᵥ (A *ᵥ Pi.single a 1) = 0 := by
      rw [Matrix.mulVec_mulVec, hQA, Matrix.zero_mulVec]
    rwa [hAa, Matrix.mulVec_add, hQL, add_zero] at hz
  have hm4 := pure_leaf_star_cycle_fourth_constraint G hI hbound a c Y hc hNa hNl l hl
  rw [hm, hd] at hm4
  norm_num at hm4
  have hm2 : (A ^ 2) c c = 6 := by
    change ((G.adjMatrix ℝ) ^ 2) c c = 6
    rw [pow_two, G.adjMatrix_mul_self_apply_self, hd]
    norm_num
  have hQcc : radiusThreeQ0 A c c = 0 := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using congrFun hQc c
  have hm6 : (A ^ 6) c c = 456 := by
    change 36 * (1 : Matrix V V ℝ) c c - 49 * (A ^ 2) c c +
      14 * (A ^ 4) c c - (A ^ 6) c c = 0 at hQcc
    rw [Matrix.one_apply_eq, hm2, hm4] at hQcc
    linarith only [hQcc]
  have hPcc : radiusThreeP4 A c c = 0 := by
    change -(A ^ 6) c c + 10 * (A ^ 4) c c - 9 * (A ^ 2) c c = 0
    rw [hm6, hm4, hm2]
    norm_num
  have hPval : Pi.single c (1 : ℝ) ⬝ᵥ radiusThreeP4 A *ᵥ Pi.single c 1 = 0 := by
    simpa only [single_dotProduct, one_mul, Matrix.mulVec_single_one,
      Matrix.col_apply] using hPcc
  obtain ⟨hPsym, hPsq⟩ := integral_radius_three_P4_relations G hI hbound
  have hPc := symmetric_scaled_idempotent_quadratic_zero
    (radiusThreeP4 A) hPsym 60 hPsq (Pi.single c 1) hPval
  exact ⟨hQc, hm6, hPc⟩
#print axioms Paper7IntroFourLeafColumn.pure_four_leaf_degree_six_zero_columns

end Paper7IntroFourLeafColumn
