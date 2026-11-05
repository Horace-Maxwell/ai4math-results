import Research.Backfill.Paper7.IntroPureFourLeafZeroColumn

/-! The two actually derived zero columns give the quadratic c-column
relation and the corrected factor 45 in the S-column transport. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroFourLeafColumn
open Matrix SimpleGraph BackfillPaper7.Challenge
open Paper7IntroFourProjector Paper7IntroZeroOneProjectors Paper7IntroProjectors
open Paper7IntroPendantFour

theorem pure_four_leaf_degree_six_spectral_columns
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3) (a c : V)
    (Y : Finset V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a)
    (l : V) (hl : l ∈ Y) (hm : Y.card = 4) (hd : G.degree c = 6) :
    radiusThreeQ0 (G.adjMatrix ℝ) *ᵥ Pi.single c 1 = 0 ∧
      ((G.adjMatrix ℝ) ^ 6) c c = 456 ∧
      radiusThreeP4 (G.adjMatrix ℝ) *ᵥ Pi.single c 1 = 0 ∧
      ((G.adjMatrix ℝ) ^ 4 - (10 : ℝ) • (G.adjMatrix ℝ) ^ 2 + (9 : ℝ) • 1) *ᵥ
        Pi.single c 1 = 0 ∧
      radiusThreeS (G.adjMatrix ℝ) *ᵥ Pi.single c 1 =
        (45 : ℝ) • (((G.adjMatrix ℝ) ^ 2 - 1) *ᵥ Pi.single c 1) := by
  let A := G.adjMatrix ℝ
  obtain ⟨hQ, hm6, hP⟩ := pure_four_leaf_degree_six_zero_columns
    G hI hbound a c Y hc hNa hNl l hl hm hd
  have hQP : radiusThreeQ0 A - radiusThreeP4 A = (4 : ℝ) • radiusThreeFactor A := by
    simp only [radiusThreeQ0, radiusThreeP4, radiusThreeFactor]
    module
  have hK4 : (4 : ℝ) • (radiusThreeFactor A *ᵥ Pi.single c 1) = 0 := by
    rw [← Matrix.smul_mulVec, ← hQP, Matrix.sub_mulVec, hQ, hP, sub_self]
  have hK : radiusThreeFactor A *ᵥ Pi.single c 1 = 0 := by
    funext v
    have hv := congrFun hK4 v
    change 4 * ((radiusThreeFactor A *ᵥ Pi.single c 1) v) = 0 at hv
    change (radiusThreeFactor A *ᵥ Pi.single c 1) v = 0
    linarith only [hv]
  have h22 : A ^ 2 * A ^ 2 = A ^ 4 := (pow_add A 2 2).symm
  have h24 : A ^ 2 * A ^ 4 = A ^ 6 := (pow_add A 2 4).symm
  have hpoly : radiusThreeS A - (45 : ℝ) • (A ^ 2 - 1) =
      (A ^ 2 + (5 : ℝ) • 1) * radiusThreeFactor A := by
    simp only [radiusThreeS, radiusThreeFactor, mul_add, mul_sub, add_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_mul, mul_one, h22, h24]
    module
  have hS : radiusThreeS A *ᵥ Pi.single c 1 =
      (45 : ℝ) • ((A ^ 2 - 1) *ᵥ Pi.single c 1) := by
    have hz : (radiusThreeS A - (45 : ℝ) • (A ^ 2 - 1)) *ᵥ Pi.single c 1 = 0 := by
      rw [hpoly, ← Matrix.mulVec_mulVec, hK, Matrix.mulVec_zero]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec] at hz
    exact sub_eq_zero.mp hz
  exact ⟨hQ, hm6, hP, hK, hS⟩
#print axioms Paper7IntroFourLeafColumn.pure_four_leaf_degree_six_spectral_columns

end Paper7IntroFourLeafColumn
