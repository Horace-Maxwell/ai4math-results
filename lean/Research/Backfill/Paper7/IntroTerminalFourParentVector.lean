import Research.Backfill.Paper7.IntroTerminalFanQuartic
import Research.Backfill.Paper7.IntroPendantFourMoments

/-! The actual parent-neighbor vector of a degree-four terminal satisfies
the radius-three factor. The generic spectral bound is stated explicitly. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroTerminalFourRemote
open Matrix SimpleGraph BackfillPaper7.Challenge
open Paper7IntroLocalQuartic Paper7IntroPendantFour

theorem integral_terminal_four_parent_vector_annihilated
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (x p : V) (hxp : G.Adj x p) (hx : G.degree x = 4)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    radiusThreeFactor (G.adjMatrix ℝ) *ᵥ
      (G.adjMatrix ℝ *ᵥ Pi.single p 1 - Pi.single x 1) = 0 := by
  let A := G.adjMatrix ℝ
  let ex : V → ℝ := Pi.single x 1
  let ep : V → ℝ := Pi.single p 1
  let z : V → ℝ := A *ᵥ ex - ep
  let u : V → ℝ := A *ᵥ ep - ex
  have hxcol : A ^ 2 *ᵥ ex = A *ᵥ ep + (3 : ℝ) • ex := by
    have h := terminal_fan_square_column G x p hxp hleaf
    norm_num [hx] at h
    simpa only [A, ex, ep, Matrix.mulVec_single_one] using h
  have hAz : A *ᵥ z = (3 : ℝ) • ex := by
    change A *ᵥ (A *ᵥ ex - ep) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← pow_two, hxcol]
    exact add_sub_cancel_left _ _
  have hA2z : A ^ 2 *ᵥ z = (3 : ℝ) • (A *ᵥ ex) := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hAz, Matrix.mulVec_smul]
  have hmove : (A * (A ^ 2 - (4 : ℝ) • 1)) *ᵥ z = (3 : ℝ) • u := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_sub, hA2z, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_two, hxcol, hAz]
    funext j
    simp only [u, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h := congrArg (fun M : Matrix V V ℝ => M *ᵥ z)
    (integral_radius_three_matrix_annihilator G hI hbound)
  rw [Matrix.zero_mulVec] at h
  change (radiusThreeFactor A * A * (A ^ 2 - (4 : ℝ) • 1)) *ᵥ z = 0 at h
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hmove, Matrix.mulVec_smul] at h
  change radiusThreeFactor A *ᵥ u = 0
  funext j
  have hj := congrFun h j
  change 3 * (radiusThreeFactor A *ᵥ u) j = 0 at hj
  change (radiusThreeFactor A *ᵥ u) j = 0
  linarith
#print axioms Paper7IntroTerminalFourRemote.integral_terminal_four_parent_vector_annihilated

end Paper7IntroTerminalFourRemote
