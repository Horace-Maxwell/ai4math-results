import Research.Backfill.Paper7.IntroPureLeafSumEvenMoments
import Research.Backfill.Paper7.IntroPureLeafStarLocalMoments
import Research.Backfill.Paper7.IntroRadiusThreePolynomialNonnegative

/-! Two necessary scalar inequalities for the same actual finite leaf star.
The zero-mode form is evaluated on the whole leaf sum, not multiplied from a
single leaf. The plus/minus-one form is evaluated at the selected true leaf. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroPureLeafMoments
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroZeroOneProjectors

theorem integral_radius_three_pure_leaf_star_polynomial_bounds
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3) (a c : V)
    (Y : Finset V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a)
    (l : V) (hl : l ∈ Y) :
    0 ≤ (Y.card : ℝ) * (36 - 35 * (Y.card : ℝ) + 12 * (Y.card : ℝ) ^ 2 -
      (Y.card : ℝ) ^ 3 - (Y.card : ℝ) * (G.degree c : ℝ)) ∧
      0 ≤ (G.degree c : ℝ) + (Y.card : ℝ) ^ 2 - 11 * (Y.card : ℝ) + 23 := by
  let A := G.adjMatrix ℝ
  let L : V → ℝ := ∑ y ∈ Y, Pi.single y 1
  let m : ℝ := Y.card
  let d : ℝ := G.degree c
  obtain ⟨hL0, _hAL, hL2, hL4, hL6⟩ := pure_leaf_star_leaf_sum_even_moments G a c Y hc hNa hNl
  change L ⬝ᵥ L = m at hL0
  change L ⬝ᵥ A ^ 2 *ᵥ L = m ^ 2 at hL2
  change L ⬝ᵥ A ^ 4 *ᵥ L = m ^ 2 * (m + 1) at hL4
  change L ⬝ᵥ A ^ 6 *ᵥ L = m ^ 2 * (m ^ 2 + 2 * m + d) at hL6
  have hQval : L ⬝ᵥ radiusThreeQ0 A *ᵥ L =
      m * (36 - 35 * m + 12 * m ^ 2 - m ^ 3 - m * d) := by
    simp only [radiusThreeQ0, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul,
      smul_eq_mul, hL0, hL2, hL4, hL6]
    ring
  obtain ⟨hm2, hm4, hm6⟩ := pure_leaf_star_leaf_even_moments G a c Y hc hNa hNl l hl
  change (A ^ 2) l l = 1 at hm2
  change (A ^ 4) l l = m + 1 at hm4
  change (A ^ 6) l l = d + m ^ 2 + 2 * m at hm6
  have hPval : radiusThreeP1 A l l = d + m ^ 2 - 11 * m + 23 := by
    simp only [radiusThreeP1, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, hm2, hm4, hm6]
    ring
  obtain ⟨hQ, hP⟩ := integral_radius_three_Q0_P1_nonnegative G hI hbound
  constructor
  · have h := hQ L
    change 0 ≤ L ⬝ᵥ radiusThreeQ0 A *ᵥ L at h
    rwa [hQval] at h
  · have h := hP (Pi.single l 1)
    change 0 ≤ (Pi.single l 1) ⬝ᵥ radiusThreeP1 A *ᵥ Pi.single l 1 at h
    simpa only [single_dotProduct, one_mul, Matrix.mulVec_single_one,
      Matrix.col_apply, hPval] using h
#print axioms Paper7IntroPureLeafMoments.integral_radius_three_pure_leaf_star_polynomial_bounds

end Paper7IntroPureLeafMoments
