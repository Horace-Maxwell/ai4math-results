import Research.Backfill.Paper7.IntroQuarticPositiveVector
import Research.Backfill.Paper7.IntroTerminalFanQuartic
import Research.Backfill.Paper7.IntroFourRootLeafExclusion

/-! Two actual leaf neighbors force original degree at least four. Only the
general adjacency-single helper is used from the successful C4 leaf module;
no C4 or single-attachment hypothesis enters these statements. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroLocalQuartic
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral

private theorem symmetric_square_quadratic_norm
    {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsSymm) (z : V → ℝ) :
    z ⬝ᵥ A ^ 2 *ᵥ z = (A *ᵥ z) ⬝ᵥ (A *ᵥ z) := by
  rw [pow_two, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hvec : z ᵥ* A = A *ᵥ z := by
    simpa only [hA.eq] using Matrix.vecMul_transpose A z
  rw [hvec]

theorem two_leaf_quartic_quadratic
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x a b : V) (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (ha : G.degree a = 1) (hb : G.degree b = 1) :
    (Pi.single a 1 + Pi.single b 1) ⬝ᵥ quarticGap (G.adjMatrix ℝ) *ᵥ
      (Pi.single a 1 + Pi.single b 1) = 4 * (G.degree x : ℝ) - 12 := by
  let A := G.adjMatrix ℝ
  let z : V → ℝ := Pi.single a 1 + Pi.single b 1
  have hcol (l : V) (hxl : G.Adj x l) (hl : G.degree l = 1) :
      A *ᵥ Pi.single l 1 = Pi.single x 1 := by
    apply Paper7IntroFourExternal.adjacency_single_one G l x
    obtain ⟨u, _hlu, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hl
    intro j
    constructor
    · intro hlj
      exact (huniq j hlj).trans (huniq x hxl.symm).symm
    · intro hjx
      exact hjx.symm ▸ hxl.symm
  have hAz : A *ᵥ z = (2 : ℝ) • Pi.single x 1 := by
    rw [show z = Pi.single a 1 + Pi.single b 1 from rfl, Matrix.mulVec_add,
      hcol a hxa ha, hcol b hxb hb, two_smul]
  have hnorm : z ⬝ᵥ z = 2 := by
    change ((Pi.single a (1 : ℝ) : V → ℝ) + Pi.single b (1 : ℝ)) ⬝ᵥ
      ((Pi.single a (1 : ℝ) : V → ℝ) + Pi.single b (1 : ℝ)) = (2 : ℝ)
    simp only [add_dotProduct, single_dotProduct, one_mul, Pi.add_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne hab, Pi.single_eq_of_ne hab.symm]
    norm_num
  have hm2 : z ⬝ᵥ A ^ 2 *ᵥ z = 4 := by
    rw [symmetric_square_quadratic_norm A G.isSymm_adjMatrix z, hAz]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul,
      single_dotProduct, Pi.single_eq_same]
    norm_num
  have hA2z : A ^ 2 *ᵥ z = (2 : ℝ) • (A *ᵥ Pi.single x 1) := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hAz, Matrix.mulVec_smul]
  have hm4 : z ⬝ᵥ A ^ 4 *ᵥ z = 4 * (G.degree x : ℝ) := by
    rw [show A ^ 4 = (A ^ 2) ^ 2 from pow_mul A 2 2,
      symmetric_square_quadratic_norm (A ^ 2) (G.isSymm_adjMatrix.pow 2) z, hA2z]
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← symmetric_square_diagonal A G.isSymm_adjMatrix x, pow_two,
      G.adjMatrix_mul_self_apply_self]
    ring
  change z ⬝ᵥ quarticGap A *ᵥ z = 4 * (G.degree x : ℝ) - 12
  rw [quarticGap, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hm4, hm2, hnorm]
  ring
#print axioms Paper7IntroLocalQuartic.two_leaf_quartic_quadratic

theorem integral_connected_two_leaf_neighbors_degree_ge_four
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (s : ℝ) (hs : s ∈ spec G) (hs2 : 2 < s)
    (x a b : V) (hab : a ≠ b) (hxa : G.Adj x a) (hxb : G.Adj x b)
    (ha : G.degree a = 1) (hb : G.degree b = 1) : 4 ≤ G.degree x := by
  let z : V → ℝ := Pi.single a 1 + Pi.single b 1
  have hz : ∀ i, 0 ≤ z i := by
    intro i
    change 0 ≤ (Pi.single a (1 : ℝ) : V → ℝ) i + (Pi.single b (1 : ℝ) : V → ℝ) i
    exact add_nonneg (by simp only [Pi.single_apply]; split_ifs <;> norm_num)
      (by simp only [Pi.single_apply]; split_ifs <;> norm_num)
  have hza : z a = 1 := by
    simp only [z, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero]
  have hp := integral_connected_quartic_nonnegative_vector_pos
    G hG hI s hs hs2 z hz ⟨a, by rw [hza]; norm_num⟩
  change 0 < (Pi.single a 1 + Pi.single b 1) ⬝ᵥ quarticGap (G.adjMatrix ℝ) *ᵥ
    (Pi.single a 1 + Pi.single b 1) at hp
  rw [two_leaf_quartic_quadratic G x a b hab hxa hxb ha hb] at hp
  have hx : (3 : ℝ) < (G.degree x : ℝ) := by linarith
  have hxN : 3 < G.degree x := by exact_mod_cast hx
  omega
#print axioms Paper7IntroLocalQuartic.integral_connected_two_leaf_neighbors_degree_ge_four

theorem integral_radius_three_small_terminal_fan_degree_two
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (hthree : (integerSpectrum G).count 3 = 1)
    (x p : V) (hxp : G.Adj x p) (hx2 : 2 ≤ G.degree x) (hx3 : G.degree x ≤ 3)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    G.degree x = 2 ∧ 4 ≤ G.degree p := by
  have hp := integral_radius_three_small_terminal_fan_parent_ge_four
    G hG hI hthree x p hxp (by omega) hleaf
  have hxne : G.degree x ≠ 3 := by
    intro hx
    have hpN : p ∈ G.neighborFinset x := (G.mem_neighborFinset x p).mpr hxp
    have hcard : ((G.neighborFinset x).erase p).card = 2 := by
      rw [Finset.card_erase_of_mem hpN, G.card_neighborFinset_eq_degree, hx]
    obtain ⟨a, b, hab, hE⟩ := Finset.card_eq_two.mp hcard
    have haE : a ∈ (G.neighborFinset x).erase p := by rw [hE]; simp
    have hbE : b ∈ (G.neighborFinset x).erase p := by rw [hE]; simp
    have hxa := (G.mem_neighborFinset x a).mp (Finset.mem_erase.mp haE).2
    have hxb := (G.mem_neighborFinset x b).mp (Finset.mem_erase.mp hbE).2
    have hm : (3 : ℤ) ∈ integerSpectrum G := Multiset.count_pos.mp (by omega)
    have hs : (3 : ℝ) ∈ spec G := by
      rw [← integerSpectrum_cast G hI]
      exact Multiset.mem_map.mpr ⟨3, hm, by norm_num⟩
    have hd := integral_connected_two_leaf_neighbors_degree_ge_four
      G hG hI 3 hs (by norm_num) x a b hab hxa hxb
      (hleaf a hxa (Finset.mem_erase.mp haE).1)
      (hleaf b hxb (Finset.mem_erase.mp hbE).1)
    omega
  exact ⟨by omega, hp⟩
#print axioms Paper7IntroLocalQuartic.integral_radius_three_small_terminal_fan_degree_two

end Paper7IntroLocalQuartic
