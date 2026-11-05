import Research.Backfill.Paper7.IntroTerminalFanQuartic
import Research.Backfill.Paper7.IntroPendantFourMoments

/-! A genuine degree-four terminal with a degree-two parent forces exact
moments at the parent's other actual neighbor. The rest of the graph is
unrestricted. The spectral interval is explicit in the generic statement. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroTerminalFourParentTwo
open Matrix SimpleGraph BackfillPaper7.Challenge
open Paper7IntroLocalQuartic Paper7IntroPendantFour

theorem integral_terminal_four_two_parent_row_moments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (x p c : V) (hxp : G.Adj x p) (hx : G.degree x = 4) (hxc : x ≠ c)
    (hp : ∀ j, G.Adj p j ↔ j = x ∨ j = c)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    radiusThreeFactor (G.adjMatrix ℝ) *ᵥ Pi.single c 1 = 0 ∧
      G.degree c = 6 ∧ ((G.adjMatrix ℝ) ^ 4) c c = 51 := by
  let A := G.adjMatrix ℝ
  let ex : V → ℝ := Pi.single x 1
  let ep : V → ℝ := Pi.single p 1
  let ec : V → ℝ := Pi.single c 1
  let z : V → ℝ := A *ᵥ ex - ep
  have hpcol : A *ᵥ ep = ex + ec :=
    adjacency_single_of_two_neighbors G p x c hxc hp
  have hxraw : A ^ 2 *ᵥ ex = A *ᵥ ep + (3 : ℝ) • ex := by
    have h := terminal_fan_square_column G x p hxp hleaf
    norm_num [hx] at h
    simpa only [A, ex, ep, Matrix.mulVec_single_one] using h
  have hxcol : A ^ 2 *ᵥ ex = (4 : ℝ) • ex + ec := by
    rw [hxraw, hpcol]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hAz : A *ᵥ z = (3 : ℝ) • ex := by
    change A *ᵥ (A *ᵥ ex - ep) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← pow_two, hxraw]
    exact add_sub_cancel_left _ _
  have hA2z : A ^ 2 *ᵥ z = (3 : ℝ) • (A *ᵥ ex) := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hAz, Matrix.mulVec_smul]
  have hmove : (A * (A ^ 2 - (4 : ℝ) • 1)) *ᵥ z = (3 : ℝ) • ec := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_sub, hA2z, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_two, hxcol, hAz]
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hz : radiusThreeFactor A *ᵥ ec = 0 := by
    have h := congrArg (fun M : Matrix V V ℝ => M *ᵥ z)
      (integral_radius_three_matrix_annihilator G hI hbound)
    rw [Matrix.zero_mulVec] at h
    change (radiusThreeFactor A * A * (A ^ 2 - (4 : ℝ) • 1)) *ᵥ z = 0 at h
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hmove, Matrix.mulVec_smul] at h
    funext j
    have hj := congrFun h j
    change 3 * (radiusThreeFactor A *ᵥ ec) j = 0 at hj
    change (radiusThreeFactor A *ᵥ ec) j = 0
    linarith
  have h2xc : (A ^ 2) x c = 1 := by
    have hsym : A.IsSymm := G.isSymm_adjMatrix
    have hcx : (A ^ 2) c x = 1 := by
      have h := congrFun hxcol c
      simpa only [ex, ec, Matrix.mulVec_single_one, Matrix.col_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hxc.symm,
        Pi.single_eq_same, mul_zero, zero_add] using h
    exact ((hsym.pow 2).apply c x).trans hcx
  have h2cc : (A ^ 2) c c = (G.degree c : ℝ) := by
    change ((G.adjMatrix ℝ) ^ 2) c c = _
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have h4xc : (A ^ 4) x c = 4 + (G.degree c : ℝ) := by
    rw [show A ^ 4 = (A ^ 2) ^ 2 from pow_mul A 2 2,
      symmetric_square_entry (A ^ 2) (G.isSymm_adjMatrix.pow 2), hxcol]
    simp only [ex, ec, add_dotProduct, smul_dotProduct, smul_eq_mul,
      single_dotProduct, one_mul, Matrix.mulVec_single_one, Matrix.col_apply,
      h2xc, h2cc, mul_one]
  have he (j : V) : (A ^ 4) j c - 10 * (A ^ 2) j c +
      9 * (1 : Matrix V V ℝ) j c = 0 := by
    have h := congrFun hz j
    simpa only [ec, Matrix.mulVec_single_one, Matrix.col_apply, radiusThreeFactor,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Pi.zero_apply] using h
  have hdR : (G.degree c : ℝ) = 6 := by
    have h := he x
    rw [h4xc, h2xc, Matrix.one_apply_ne hxc] at h
    linarith
  have hd : G.degree c = 6 := by exact_mod_cast hdR
  refine ⟨hz, hd, ?_⟩
  have h := he c
  rw [h2cc, hdR, Matrix.one_apply_eq] at h
  change (A ^ 4) c c = 51
  linarith
#print axioms Paper7IntroTerminalFourParentTwo.integral_terminal_four_two_parent_row_moments

theorem integral_terminal_four_degree_two_parent_moments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (x p : V) (hxp : G.Adj x p) (hx : G.degree x = 4) (hp : G.degree p = 2)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    ∃ c : V, c ≠ x ∧ G.Adj p c ∧
      (∀ j, G.Adj p j ↔ j = x ∨ j = c) ∧
      radiusThreeFactor (G.adjMatrix ℝ) *ᵥ Pi.single c 1 = 0 ∧
      G.degree c = 6 ∧ ((G.adjMatrix ℝ) ^ 4) c c = 51 := by
  have hxN : x ∈ G.neighborFinset p := (G.mem_neighborFinset p x).mpr hxp.symm
  have hcard : ((G.neighborFinset p).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hxN, G.card_neighborFinset_eq_degree, hp]
  obtain ⟨c, hE⟩ := Finset.card_eq_one.mp hcard
  have hcE : c ∈ (G.neighborFinset p).erase x := by rw [hE]; simp
  have hcx : c ≠ x := (Finset.mem_erase.mp hcE).1
  have hpc : G.Adj p c := (G.mem_neighborFinset p c).mp (Finset.mem_erase.mp hcE).2
  have hrow : ∀ j, G.Adj p j ↔ j = x ∨ j = c := by
    intro j
    constructor
    · intro hpj
      by_cases hjx : j = x
      · exact Or.inl hjx
      · right
        have hjE : j ∈ (G.neighborFinset p).erase x :=
          Finset.mem_erase.mpr ⟨hjx, (G.mem_neighborFinset p j).mpr hpj⟩
        rwa [hE, Finset.mem_singleton] at hjE
    · rintro (rfl | rfl)
      · exact hxp.symm
      · exact hpc
  exact ⟨c, hcx, hpc, hrow,
    integral_terminal_four_two_parent_row_moments G hI hbound x p c hxp hx hcx.symm hrow hleaf⟩
#print axioms Paper7IntroTerminalFourParentTwo.integral_terminal_four_degree_two_parent_moments

end Paper7IntroTerminalFourParentTwo
