import Research.Backfill.Paper7.IntroSymmetricScaledKernel

/-! The scaled plus/minus-two spectral polynomial is derived from the
actual seven-root annihilator through the already proved Q0*A relation.
No projector, rank, moment value, or local graph shape is a premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroFourProjector
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroZeroOneProjectors

def radiusThreeP4 {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : Matrix V V ℝ := by
  exact -A ^ 6 + (10 : ℝ) • A ^ 4 - (9 : ℝ) • A ^ 2
#print axioms Paper7IntroFourProjector.radiusThreeP4

theorem radiusThreeP4_factored
    {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) :
    radiusThreeP4 A = -(A ^ 2 * (A ^ 2 - 1) * (A ^ 2 - (9 : ℝ) • 1)) := by
  have h22 : A ^ 2 * A ^ 2 = A ^ 4 := (pow_add A 2 2).symm
  have h42 : A ^ 4 * A ^ 2 = A ^ 6 := (pow_add A 4 2).symm
  simp only [radiusThreeP4, mul_sub, sub_mul, Matrix.mul_smul, mul_one, h22, h42]
  module
#print axioms Paper7IntroFourProjector.radiusThreeP4_factored

theorem integral_radius_three_P4_relations
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3) :
    (radiusThreeP4 (G.adjMatrix ℝ)).IsSymm ∧
      radiusThreeP4 (G.adjMatrix ℝ) ^ 2 =
        (60 : ℝ) • radiusThreeP4 (G.adjMatrix ℝ) := by
  let A := G.adjMatrix ℝ
  have hA : A.IsSymm := G.isSymm_adjMatrix
  have hQA := (integral_radius_three_Q0_P1_relations G hI hbound).1
  change radiusThreeQ0 A * A = 0 at hQA
  have h22 : A ^ 2 * A ^ 2 = A ^ 4 := (pow_add A 2 2).symm
  have h42 : A ^ 4 * A ^ 2 = A ^ 6 := (pow_add A 4 2).symm
  have h62 : A ^ 6 * A ^ 2 = A ^ 8 := (pow_add A 6 2).symm
  have heven : A ^ 8 - (14 : ℝ) • A ^ 6 + (49 : ℝ) • A ^ 4 -
      (36 : ℝ) • A ^ 2 = 0 := by
    have hz : radiusThreeQ0 A * A ^ 2 = 0 := by
      rw [pow_two, ← mul_assoc, hQA, zero_mul]
    have he : radiusThreeQ0 A * A ^ 2 =
        -(A ^ 8 - (14 : ℝ) • A ^ 6 + (49 : ℝ) • A ^ 4 -
          (36 : ℝ) • A ^ 2) := by
      simp only [radiusThreeQ0, add_mul, sub_mul, Matrix.smul_mul, one_mul,
        h22, h42, h62]
      module
    rw [he] at hz
    exact neg_eq_zero.mp hz
  constructor
  · exact (((hA.pow 6).neg).add ((hA.pow 4).smul 10)).sub ((hA.pow 2).smul 9)
  · change radiusThreeP4 A ^ 2 = (60 : ℝ) • radiusThreeP4 A
    apply sub_eq_zero.mp
    calc
      _ = (A ^ 8 - (14 : ℝ) • A ^ 6 + (49 : ℝ) • A ^ 4 -
            (36 : ℝ) • A ^ 2) * (A ^ 4 - (6 : ℝ) • A ^ 2 - (15 : ℝ) • 1) := by
        rw [pow_two]
        simp only [radiusThreeP4, add_mul, sub_mul, mul_add, mul_sub,
          neg_mul, mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          mul_one, ← pow_add]
        module
      _ = 0 := by rw [heven, zero_mul]
#print axioms Paper7IntroFourProjector.integral_radius_three_P4_relations

end Paper7IntroFourProjector
