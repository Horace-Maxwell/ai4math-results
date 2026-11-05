import Research.Backfill.Paper7.IntroTerminalFourParentVector

/-! The norm forced by the successful terminal-four parent annihilator.
No component radius statement or restriction on the parent's other neighbors
is used here. The spectral interval is an explicit generic hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroTerminalFourRemote
open Matrix SimpleGraph BackfillPaper7.Challenge
open Paper7IntroLocalQuartic Paper7IntroPendantFour

private theorem symmetric_dot_mulVec
    {V : Type} [Fintype V] (A : Matrix V V ℝ) (hA : A.IsSymm)
    (v w : V → ℝ) : v ⬝ᵥ A *ᵥ w = (A *ᵥ v) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec]
  have hv : v ᵥ* A = A *ᵥ v := by
    simpa only [hA.eq] using Matrix.vecMul_transpose A v
  rw [hv]

theorem integral_terminal_four_parent_vector_norm
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (x p : V) (hxp : G.Adj x p) (hx : G.degree x = 4)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    let u := G.adjMatrix ℝ *ᵥ Pi.single p 1 - Pi.single x 1
    u ⬝ᵥ u = (G.degree p : ℝ) - 1 ∧
      (G.adjMatrix ℝ *ᵥ u) ⬝ᵥ (G.adjMatrix ℝ *ᵥ u) =
        6 * ((G.degree p : ℝ) - 1) := by
  let A := G.adjMatrix ℝ
  let ex : V → ℝ := Pi.single x 1
  let ep : V → ℝ := Pi.single p 1
  let c : V → ℝ := A *ᵥ ep
  let u : V → ℝ := c - ex
  have hA : A.IsSymm := G.isSymm_adjMatrix
  have hc : c ⬝ᵥ c = (G.degree p : ℝ) := by
    rw [← symmetric_square_diagonal A hA p, pow_two,
      G.adjMatrix_mul_self_apply_self]
  have hcx : c x = 1 := by
    change (G.adjMatrix ℝ *ᵥ Pi.single p 1) x = 1
    rw [Matrix.mulVec_single_one]
    exact ite_eq_left hxp
  have hu0 : u x = 0 := by
    change c x - (Pi.single x (1 : ℝ) : V → ℝ) x = 0
    rw [hcx, Pi.single_eq_same, sub_self]
  have hnorm : u ⬝ᵥ u = (G.degree p : ℝ) - 1 := by
    change (c - ex) ⬝ᵥ (c - ex) = _
    simp only [sub_dotProduct, dotProduct_sub, ex, single_dotProduct,
      dotProduct_single, mul_one, hc, hcx]
    rw [Pi.sub_apply, Pi.single_eq_same, hcx]
    ring
  have hxcol : A ^ 2 *ᵥ ex = u + (4 : ℝ) • ex := by
    have hxraw : A ^ 2 *ᵥ ex = A *ᵥ ep + (3 : ℝ) • ex := by
      have h := terminal_fan_square_column G x p hxp hleaf
      norm_num [hx] at h
      simpa only [A, ex, ep, Matrix.mulVec_single_one] using h
    rw [hxraw]
    funext j
    simp only [u, c, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : (A ^ 2 *ᵥ u) x = u ⬝ᵥ u := by
    calc
      (A ^ 2 *ᵥ u) x = ex ⬝ᵥ A ^ 2 *ᵥ u := by
        simp only [ex, single_dotProduct, one_mul]
      _ = (A ^ 2 *ᵥ ex) ⬝ᵥ u := symmetric_dot_mulVec _ (hA.pow 2) _ _
      _ = u ⬝ᵥ u := by
        rw [hxcol]
        simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, ex,
          single_dotProduct, hu0, mul_zero, add_zero]
  have hnormA : u ⬝ᵥ A ^ 2 *ᵥ u = (A *ᵥ u) ⬝ᵥ (A *ᵥ u) := by
    rw [pow_two, ← Matrix.mulVec_mulVec]
    exact symmetric_dot_mulVec A hA u (A *ᵥ u)
  have h4 : (A ^ 4 *ᵥ u) x =
      (A *ᵥ u) ⬝ᵥ (A *ᵥ u) + 4 * (u ⬝ᵥ u) := by
    calc
      (A ^ 4 *ᵥ u) x = ex ⬝ᵥ A ^ 2 *ᵥ (A ^ 2 *ᵥ u) := by
        rw [Matrix.mulVec_mulVec, ← pow_add]
        simp only [ex, single_dotProduct, one_mul]
      _ = (A ^ 2 *ᵥ ex) ⬝ᵥ (A ^ 2 *ᵥ u) :=
        symmetric_dot_mulVec _ (hA.pow 2) _ _
      _ = (A *ᵥ u) ⬝ᵥ (A *ᵥ u) + 4 * (u ⬝ᵥ u) := by
        rw [hxcol]
        simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, ex,
          single_dotProduct, one_mul, hnormA, h2]
  have hz := integral_terminal_four_parent_vector_annihilated G hI hbound x p hxp hx hleaf
  change radiusThreeFactor A *ᵥ u = 0 at hz
  have hzX := congrFun hz x
  have he : (A ^ 4 *ᵥ u) x - 10 * (A ^ 2 *ᵥ u) x + 9 * u x = 0 := by
    simpa only [radiusThreeFactor, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hzX
  rw [h4, h2, hu0, hnorm] at he
  change u ⬝ᵥ u = _ ∧ (A *ᵥ u) ⬝ᵥ (A *ᵥ u) = _
  exact ⟨hnorm, by linarith⟩
#print axioms Paper7IntroTerminalFourRemote.integral_terminal_four_parent_vector_norm

end Paper7IntroTerminalFourRemote
