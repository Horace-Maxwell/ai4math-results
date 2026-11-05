import Research.Backfill.Paper7.IntroTerminalFanQuartic

/-! Two terminal fans sharing their actual parent give a signed quartic
test vector. The rest of the graph is arbitrary. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroTerminalCompetition
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroLocalQuartic

private theorem symmetric_square_quadratic_norm
    {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsSymm) (z : V → ℝ) :
    z ⬝ᵥ A ^ 2 *ᵥ z = (A *ᵥ z) ⬝ᵥ (A *ᵥ z) := by
  rw [pow_two, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hvec : z ᵥ* A = A *ᵥ z := by
    simpa only [hA.eq] using Matrix.vecMul_transpose A z
  rw [hvec]

theorem terminal_fan_difference_quartic
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y p : V) (hxy : x ≠ y) (hxp : G.Adj x p) (hyp : G.Adj y p)
    (hxleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1)
    (hyleaf : ∀ j, G.Adj y j → j ≠ p → G.degree j = 1) :
    (Pi.single x 1 - Pi.single y 1) ⬝ᵥ quarticGap (G.adjMatrix ℝ) *ᵥ
      (Pi.single x 1 - Pi.single y 1) =
      (((G.degree x - 1 : ℕ) : ℝ)) ^ 2 + (((G.degree y - 1 : ℕ) : ℝ)) ^ 2 -
        5 * (((G.degree x - 1 : ℕ) : ℝ) + ((G.degree y - 1 : ℕ) : ℝ)) + 8 := by
  let A := G.adjMatrix ℝ
  let z : V → ℝ := Pi.single x 1 - Pi.single y 1
  let tx : ℝ := (G.degree x - 1 : ℕ)
  let ty : ℝ := (G.degree y - 1 : ℕ)
  have h2 : A ^ 2 *ᵥ z = tx • Pi.single x 1 - ty • Pi.single y 1 := by
    dsimp only [tx, ty]
    change A ^ 2 *ᵥ (Pi.single x 1 - Pi.single y 1) = _
    rw [Matrix.mulVec_sub, terminal_fan_square_column G x p hxp hxleaf,
      terminal_fan_square_column G y p hyp hyleaf]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hzx : z x = 1 := by
    simp only [z, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hxy, sub_zero]
  have hzy : z y = -1 := by
    simp only [z, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hxy.symm, zero_sub]
  have hnorm : z ⬝ᵥ z = 2 := by
    change ((Pi.single x (1 : ℝ) : V → ℝ) - Pi.single y (1 : ℝ)) ⬝ᵥ
      ((Pi.single x (1 : ℝ) : V → ℝ) - Pi.single y (1 : ℝ)) = (2 : ℝ)
    simp only [sub_dotProduct, single_dotProduct, one_mul, Pi.sub_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne hxy, Pi.single_eq_of_ne hxy.symm]
    norm_num
  have hm2 : z ⬝ᵥ A ^ 2 *ᵥ z = tx + ty := by
    simp only [h2, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      dotProduct_single, mul_one, hzx, hzy]
    ring
  have hm4 : z ⬝ᵥ A ^ 4 *ᵥ z = tx ^ 2 + ty ^ 2 := by
    rw [show A ^ 4 = (A ^ 2) ^ 2 from pow_mul A 2 2,
      symmetric_square_quadratic_norm (A ^ 2) (G.isSymm_adjMatrix.pow 2) z, h2]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, single_dotProduct, Pi.single_eq_same,
      Pi.single_eq_of_ne hxy, Pi.single_eq_of_ne hxy.symm]
    ring
  change z ⬝ᵥ quarticGap A *ᵥ z = tx ^ 2 + ty ^ 2 - 5 * (tx + ty) + 8
  rw [quarticGap, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hm4, hm2, hnorm]
  ring
#print axioms Paper7IntroTerminalCompetition.terminal_fan_difference_quartic

theorem integral_degree_four_terminal_unique_small_terminal_sibling
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (x y p : V) (hxp : G.Adj x p) (hyp : G.Adj y p)
    (hx : G.degree x = 4) (hy2 : 2 ≤ G.degree y) (hy5 : G.degree y ≤ 5)
    (hxleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1)
    (hyleaf : ∀ j, G.Adj y j → j ≠ p → G.degree j = 1) : x = y := by
  by_contra hxy
  have hn : 0 ≤ (Pi.single x 1 - Pi.single y 1) ⬝ᵥ
      quarticGap (G.adjMatrix ℝ) *ᵥ (Pi.single x 1 - Pi.single y 1) := by
    simpa only [star_trivial] using (integral_quarticGap_posSemidef G hI).dotProduct_mulVec_nonneg
      (Pi.single x 1 - Pi.single y 1)
  rw [terminal_fan_difference_quartic G x y p hxy hxp hyp hxleaf hyleaf] at hn
  have htx : (((G.degree x - 1 : ℕ) : ℝ)) = 3 := by rw [hx]; norm_num
  rw [htx] at hn
  let t : ℝ := (G.degree y - 1 : ℕ)
  have htN : 1 ≤ G.degree y - 1 ∧ G.degree y - 1 ≤ 4 := by omega
  have htlo : (1 : ℝ) ≤ t := by
    change (1 : ℝ) ≤ ((G.degree y - 1 : ℕ) : ℝ)
    exact_mod_cast htN.1
  have hthi : t ≤ (4 : ℝ) := by
    change ((G.degree y - 1 : ℕ) : ℝ) ≤ (4 : ℝ)
    exact_mod_cast htN.2
  have hprod : (t - 1) * (t - 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr htlo) (sub_nonpos.mpr hthi)
  change 0 ≤ (3 : ℝ) ^ 2 + t ^ 2 - 5 * (3 + t) + 8 at hn
  nlinarith
#print axioms Paper7IntroTerminalCompetition.integral_degree_four_terminal_unique_small_terminal_sibling

end Paper7IntroTerminalCompetition
