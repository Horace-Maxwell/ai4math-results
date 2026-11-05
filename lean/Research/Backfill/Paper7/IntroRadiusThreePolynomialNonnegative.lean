import Research.Backfill.Paper7.IntroRadiusThreeScaledPolynomial

/-! Nonnegative quadratic forms for the full zero mode and the combined
plus/minus-one modes. No local graph shape or leaf aggregation is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroZeroOneProjectors
open Matrix SimpleGraph BackfillPaper7.Challenge

theorem integral_radius_three_Q0_P1_nonnegative
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3) :
    (∀ v : V → ℝ, 0 ≤ v ⬝ᵥ radiusThreeQ0 (G.adjMatrix ℝ) *ᵥ v) ∧
      (∀ v : V → ℝ, 0 ≤ v ⬝ᵥ radiusThreeP1 (G.adjMatrix ℝ) *ᵥ v) := by
  let A := G.adjMatrix ℝ
  have hA : A.IsSymm := G.isSymm_adjMatrix
  obtain ⟨_hQA, hQsq, hPsq⟩ := integral_radius_three_Q0_P1_relations G hI hbound
  have hQ : (radiusThreeQ0 A).IsSymm :=
    (((Matrix.isSymm_one.smul (36 : ℝ)).sub ((hA.pow 2).smul 49)).add
      ((hA.pow 4).smul 14)).sub (hA.pow 6)
  have hP : (radiusThreeP1 A).IsSymm :=
    ((hA.pow 6).sub ((hA.pow 4).smul 13)).add ((hA.pow 2).smul 36)
  constructor
  · intro v
    exact symmetric_scaled_idempotent_nonnegative (radiusThreeQ0 A) hQ 36
      (by norm_num) hQsq v
  · intro v
    exact symmetric_scaled_idempotent_nonnegative (radiusThreeP1 A) hP 24
      (by norm_num) hPsq v
#print axioms Paper7IntroZeroOneProjectors.integral_radius_three_Q0_P1_nonnegative

end Paper7IntroZeroOneProjectors
