import Research.Backfill.Paper7.IntroSubdividedArmLeafMoments
import Research.Backfill.Paper7.IntroIntegralRadiusThreeAnnihilator

/-! Remove the (A²-I) factor using an actual two-edge arm. The even
diagonal relation is obtained only after multiplying the reduced vector
annihilator by A; an odd diagonal identity is never substituted for it. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroStarConstraints
open Matrix SimpleGraph BackfillPaper7.Challenge
open Paper7IntroAttachmentMoments Paper7IntroPendantFour

theorem subdivided_arm_attachment_reduced_annihilator
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hI : IsIntegralGraph G) (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (a y l : V) (hal : a ≠ l)
    (hy : ∀ z, G.Adj y z ↔ z = a ∨ z = l)
    (hl : ∀ z, G.Adj l z ↔ z = y) :
    (G.adjMatrix ℝ * ((G.adjMatrix ℝ) ^ 2 - (4 : ℝ) • 1) *
      ((G.adjMatrix ℝ) ^ 2 - (9 : ℝ) • 1)) *ᵥ Pi.single a 1 = 0 := by
  let A := G.adjMatrix ℝ
  let B := A * (A ^ 2 - (4 : ℝ) • 1) * (A ^ 2 - (9 : ℝ) • 1)
  let ea : V → ℝ := Pi.single a 1
  let el : V → ℝ := Pi.single l 1
  have h12 : A * A ^ 2 = A ^ 3 := (pow_succ' A 2).symm
  have h32 : A ^ 3 * A ^ 2 = A ^ 5 := (pow_add A 3 2).symm
  have h52 : A ^ 5 * A ^ 2 = A ^ 7 := (pow_add A 5 2).symm
  have h41 : A ^ 4 * A = A ^ 5 := (pow_succ A 4).symm
  have h21 : A ^ 2 * A = A ^ 3 := (pow_succ A 2).symm
  have hB : B = A ^ 5 - (13 : ℝ) • A ^ 3 + (36 : ℝ) • A := by
    dsimp only [B]
    simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, smul_smul, h12, h32]
    module
  have hfactor : B * (A ^ 2 - 1) =
      radiusThreeFactor A * A * (A ^ 2 - (4 : ℝ) • 1) := by
    simp only [hB, radiusThreeFactor, add_mul, sub_mul, mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul, smul_smul,
      h41, h21, h52, h32, h12]
    module
  have hz : B * (A ^ 2 - 1) = 0 := by
    rw [hfactor]
    exact integral_radius_three_matrix_annihilator G hI hbound
  have hsq : A ^ 2 *ᵥ el = ea + el :=
    subdivided_arm_square_column G a y l hal hy hl
  have hdiff : (A ^ 2 - 1) *ᵥ el = ea := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hsq]
    abel
  change B *ᵥ ea = 0
  calc
    B *ᵥ ea = B *ᵥ ((A ^ 2 - 1) *ᵥ el) := by rw [hdiff]
    _ = (B * (A ^ 2 - 1)) *ᵥ el := Matrix.mulVec_mulVec el B (A ^ 2 - 1)
    _ = 0 := by rw [hz, Matrix.zero_mulVec]
#print axioms Paper7IntroStarConstraints.subdivided_arm_attachment_reduced_annihilator

theorem subdivided_arm_attachment_even_relation
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hI : IsIntegralGraph G) (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (a y l : V) (hal : a ≠ l)
    (hy : ∀ z, G.Adj y z ↔ z = a ∨ z = l)
    (hl : ∀ z, G.Adj l z ↔ z = y) :
    ((G.adjMatrix ℝ) ^ 6) a a - 13 * ((G.adjMatrix ℝ) ^ 4) a a +
      36 * (G.degree a : ℝ) = 0 := by
  let A := G.adjMatrix ℝ
  let B := A * (A ^ 2 - (4 : ℝ) • 1) * (A ^ 2 - (9 : ℝ) • 1)
  let ea : V → ℝ := Pi.single a 1
  have hz : B *ᵥ ea = 0 :=
    subdivided_arm_attachment_reduced_annihilator G hI hbound a y l hal hy hl
  have h11 : A * A = A ^ 2 := (pow_two A).symm
  have h12 : A * A ^ 2 = A ^ 3 := (pow_succ' A 2).symm
  have h32 : A ^ 3 * A ^ 2 = A ^ 5 := (pow_add A 3 2).symm
  have h13 : A * A ^ 3 = A ^ 4 := (pow_succ' A 3).symm
  have h15 : A * A ^ 5 = A ^ 6 := (pow_succ' A 5).symm
  have hAB : A * B = A ^ 6 - (13 : ℝ) • A ^ 4 + (36 : ℝ) • A ^ 2 := by
    dsimp only [B]
    simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, smul_smul, h12, h32, h15, h13, h11]
    module
  have heven := congrArg (fun v : V → ℝ => A *ᵥ v) hz
  rw [Matrix.mulVec_mulVec, hAB, Matrix.mulVec_zero] at heven
  change (A ^ 6 - (13 : ℝ) • A ^ 4 + (36 : ℝ) • A ^ 2) *ᵥ Pi.single a 1 = 0 at heven
  rw [Matrix.mulVec_single_one] at heven
  have hdiag := congrFun heven a
  change (A ^ 6 - (13 : ℝ) • A ^ 4 + (36 : ℝ) • A ^ 2) a a = 0 at hdiag
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hdiag
  have h2 : (A ^ 2) a a = (G.degree a : ℝ) := by
    change ((G.adjMatrix ℝ) ^ 2) a a = _
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  change (A ^ 6) a a - 13 * (A ^ 4) a a + 36 * (G.degree a : ℝ) = 0
  simpa only [h2] using hdiag
#print axioms Paper7IntroStarConstraints.subdivided_arm_attachment_even_relation

end Paper7IntroStarConstraints
