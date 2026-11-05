import Research.Backfill.Paper7.IntroTerminalFanQuartic

/-! A single actual degree-four terminal gives a quartic constraint at its
parent. No restriction on the remainder of the graph is imposed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroTerminalFourParent
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroLocalQuartic

theorem degree_four_terminal_leaf_vector_quartic
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x p : V) (hxp : G.Adj x p) (hx : G.degree x = 4)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    (G.adjMatrix ℝ *ᵥ Pi.single x 1 - Pi.single p 1) ⬝ᵥ
        quarticGap (G.adjMatrix ℝ) *ᵥ
          (G.adjMatrix ℝ *ᵥ Pi.single x 1 - Pi.single p 1) = 3 ∧
      (quarticGap (G.adjMatrix ℝ) *ᵥ
        (G.adjMatrix ℝ *ᵥ Pi.single x 1 - Pi.single p 1)) p =
          3 * ((G.degree p : ℝ) - 2) := by
  let A := G.adjMatrix ℝ
  let ex : V → ℝ := Pi.single x 1
  let ep : V → ℝ := Pi.single p 1
  let z : V → ℝ := A *ᵥ ex - ep
  change z ⬝ᵥ quarticGap A *ᵥ z = 3 ∧ (quarticGap A *ᵥ z) p = _
  have hxcol : A ^ 2 *ᵥ ex = A *ᵥ ep + (3 : ℝ) • ex := by
    have hh := terminal_fan_square_column G x p hxp hleaf
    norm_num [hx] at hh
    simpa only [A, ex, ep, Matrix.mulVec_single_one] using hh
  have hAz : A *ᵥ z = (3 : ℝ) • ex := by
    change A *ᵥ (A *ᵥ ex - ep) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← pow_two, hxcol]
    exact add_sub_cancel_left _ _
  have hA2z : A ^ 2 *ᵥ z = (3 : ℝ) • (A *ᵥ ex) := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hAz, Matrix.mulVec_smul]
  have hcube : A ^ 2 *ᵥ (A *ᵥ ex) = A *ᵥ (A ^ 2 *ᵥ ex) := by
    simp only [pow_two, ← Matrix.mulVec_mulVec]
  have hA4z : A ^ 4 *ᵥ z =
      (3 : ℝ) • (A ^ 2 *ᵥ ep + (3 : ℝ) • (A *ᵥ ex)) := by
    rw [show A ^ 4 = A ^ 2 * A ^ 2 from pow_add A 2 2,
      ← Matrix.mulVec_mulVec, hA2z, Matrix.mulVec_smul, hcube, hxcol,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_two]
  have hQz : quarticGap A *ᵥ z =
      (3 : ℝ) • (A ^ 2 *ᵥ ep) - (2 : ℝ) • (A *ᵥ ex) - (4 : ℝ) • ep := by
    rw [quarticGap, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, hA4z, hA2z]
    funext i
    simp only [z, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hpx : (A *ᵥ ex) p = 1 := by
    change (G.adjMatrix ℝ *ᵥ Pi.single x 1) p = 1
    rw [Matrix.mulVec_single_one]
    exact ite_eq_left hxp.symm
  have hcx : (A *ᵥ ep) x = 1 := by
    change (G.adjMatrix ℝ *ᵥ Pi.single p 1) x = 1
    rw [Matrix.mulVec_single_one]
    exact ite_eq_left hxp
  have hep : ep p = 1 := Pi.single_eq_same p 1
  have hzp : z p = 0 := by
    change (A *ᵥ ex) p - ep p = 0
    rw [hpx, hep]
    norm_num
  have hnormcol : (A *ᵥ ex) ⬝ᵥ (A *ᵥ ex) = 4 := by
    change (A *ᵥ Pi.single x 1) ⬝ᵥ (A *ᵥ Pi.single x 1) = 4
    rw [← symmetric_square_diagonal A G.isSymm_adjMatrix x, pow_two,
      G.adjMatrix_mul_self_apply_self, hx]
    norm_num
  have hzAx : z ⬝ᵥ (A *ᵥ ex) = 3 := by
    change (A *ᵥ ex - Pi.single p 1) ⬝ᵥ (A *ᵥ ex) = 3
    rw [sub_dotProduct, hnormcol, single_dotProduct, one_mul, hpx]
    norm_num
  have hzE : z ⬝ᵥ ep = 0 := by
    change z ⬝ᵥ Pi.single p 1 = 0
    rw [dotProduct_single, mul_one, hzp]
  have hzvec : z ᵥ* A = A *ᵥ z := by
    have hsymA : A.IsSymm := G.isSymm_adjMatrix
    simpa only [hsymA.eq] using Matrix.vecMul_transpose A z
  have hzA2p : z ⬝ᵥ (A ^ 2 *ᵥ ep) = 3 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hzvec, hAz]
    change ((3 : ℝ) • Pi.single x 1) ⬝ᵥ (A *ᵥ ep) = 3
    rw [smul_dotProduct, smul_eq_mul, single_dotProduct, one_mul, hcx]
    norm_num
  have hdiagp : (A ^ 2 *ᵥ ep) p = (G.degree p : ℝ) := by
    change ((G.adjMatrix ℝ) ^ 2 *ᵥ Pi.single p 1) p = _
    rw [Matrix.mulVec_single_one, pow_two]
    change (G.adjMatrix ℝ * G.adjMatrix ℝ) p p = _
    exact G.adjMatrix_mul_self_apply_self p
  constructor
  · rw [hQz]
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, hzA2p, hzAx, hzE]
    norm_num
  · rw [hQz]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hdiagp, hpx, hep]
    ring
#print axioms Paper7IntroTerminalFourParent.degree_four_terminal_leaf_vector_quartic

theorem integral_degree_four_terminal_parent_quartic_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (x p : V) (hxp : G.Adj x p) (hx : G.degree x = 4)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    3 * ((G.degree p : ℝ) - 2) ^ 2 ≤ quarticGap (G.adjMatrix ℝ) p p := by
  let Q := quarticGap (G.adjMatrix ℝ)
  let z : V → ℝ := G.adjMatrix ℝ *ᵥ Pi.single x 1 - Pi.single p 1
  let c : ℝ := (G.degree p : ℝ) - 2
  let ep : V → ℝ := Pi.single p 1
  obtain ⟨hzz, hzp⟩ := degree_four_terminal_leaf_vector_quartic G x p hxp hx hleaf
  change z ⬝ᵥ Q *ᵥ z = 3 at hzz
  change (Q *ᵥ z) p = 3 * c at hzp
  have hQ := integral_quarticGap_posSemidef G hI
  have hsym : Q.IsSymm := Matrix.isHermitian_iff_isSymm.mp hQ.isHermitian
  have hvec : z ᵥ* Q = Q *ᵥ z := by
    simpa only [hsym.eq] using Matrix.vecMul_transpose Q z
  have hzp' : z ⬝ᵥ Q *ᵥ ep = 3 * c := by
    rw [Matrix.dotProduct_mulVec, hvec]
    change (Q *ᵥ z) ⬝ᵥ Pi.single p 1 = _
    rw [dotProduct_single, mul_one, hzp]
  have hpz : ep ⬝ᵥ Q *ᵥ z = 3 * c := by
    change Pi.single p 1 ⬝ᵥ Q *ᵥ z = _
    rw [single_dotProduct, one_mul, hzp]
  have hpp : ep ⬝ᵥ Q *ᵥ ep = Q p p := by
    change Pi.single p 1 ⬝ᵥ Q *ᵥ Pi.single p 1 = _
    rw [single_dotProduct, one_mul, Matrix.mulVec_single_one]
    rfl
  have hn : 0 ≤ (ep - c • z) ⬝ᵥ Q *ᵥ (ep - c • z) := by
    simpa only [star_trivial] using hQ.dotProduct_mulVec_nonneg (ep - c • z)
  have hf : (ep - c • z) ⬝ᵥ Q *ᵥ (ep - c • z) = Q p p - 3 * c ^ 2 := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
      dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hpp, hpz, hzp', hzz]
    ring
  rw [hf] at hn
  change 3 * c ^ 2 ≤ Q p p
  linarith
#print axioms Paper7IntroTerminalFourParent.integral_degree_four_terminal_parent_quartic_bound

end Paper7IntroTerminalFourParent
