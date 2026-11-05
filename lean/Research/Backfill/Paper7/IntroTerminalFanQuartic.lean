import Research.Backfill.Paper7.IntroIntegralDegreeTwoChain
import Research.Backfill.Paper7.IntegerSpectrum

/-! A terminal fan is taken from the actual original neighbor set. No rooted
tree profile or restriction on the rest of the graph is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroLocalQuartic
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7OddIntegral

theorem terminal_fan_square_column
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x p : V) (hxp : G.Adj x p)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    (G.adjMatrix ℝ) ^ 2 *ᵥ Pi.single x 1 =
      G.adjMatrix ℝ *ᵥ Pi.single p 1 +
        (((G.degree x - 1 : ℕ) : ℝ)) • Pi.single x 1 := by
  let E := (G.neighborFinset x).erase p
  have hpN : p ∈ G.neighborFinset x := (G.mem_neighborFinset x p).mpr hxp
  have hEcard : E.card = G.degree x - 1 := by
    rw [Finset.card_erase_of_mem hpN, G.card_neighborFinset_eq_degree]
  have hcol (k : V) (hk : k ∈ E) (j : V) :
      G.adjMatrix ℝ j k = (Pi.single x (1 : ℝ) : V → ℝ) j := by
    have hxk : G.Adj x k := (G.mem_neighborFinset x k).mp (Finset.mem_erase.mp hk).2
    have hd := hleaf k hxk (Finset.mem_erase.mp hk).1
    obtain ⟨_t, _hkt, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd
    have hadj : G.Adj j k ↔ j = x := by
      constructor
      · intro hjk
        exact (huniq j hjk.symm).trans (huniq x hxk.symm).symm
      · intro hjx
        exact hjx.symm ▸ hxk
    change (if G.Adj j k then (1 : ℝ) else 0) = _
    by_cases hjx : j = x
    · subst j
      rw [ite_eq_left hxk, Pi.single_eq_same]
    · rw [ite_eq_right (fun h => hjx (hadj.mp h)),
        Pi.single_eq_of_ne (M := fun _ : V => ℝ) hjx (1 : ℝ)]
  funext j
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one, pow_two]
  change (G.adjMatrix ℝ * G.adjMatrix ℝ) j x =
    G.adjMatrix ℝ j p + ((G.degree x - 1 : ℕ) : ℝ) * (Pi.single x (1 : ℝ) : V → ℝ) j
  rw [G.mul_adjMatrix_apply]
  rw [← Finset.add_sum_erase (G.neighborFinset x) (fun k => G.adjMatrix ℝ j k) hpN]
  have hs : (∑ k ∈ E, G.adjMatrix ℝ j k) =
      ∑ _k ∈ E, (Pi.single x (1 : ℝ) : V → ℝ) j :=
    Finset.sum_congr rfl (fun k hk => hcol k hk j)
  rw [hs, Finset.sum_const, nsmul_eq_mul, hEcard]
#print axioms Paper7IntroLocalQuartic.terminal_fan_square_column

theorem terminal_fan_quartic_diagonal
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x p : V) (hxp : G.Adj x p)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    quarticGap (G.adjMatrix ℝ) x x =
      (G.degree p : ℝ) + (((G.degree x - 1 : ℕ) : ℝ)) ^ 2 -
        3 * (((G.degree x - 1 : ℕ) : ℝ)) - 1 := by
  let A := G.adjMatrix ℝ
  let t : ℝ := (G.degree x - 1 : ℕ)
  let c := A *ᵥ Pi.single p 1
  have h2 : A ^ 2 *ᵥ Pi.single x 1 = c + t • Pi.single x 1 :=
    terminal_fan_square_column G x p hxp hleaf
  have hc : c ⬝ᵥ c = (G.degree p : ℝ) := by
    rw [← symmetric_square_diagonal A G.isSymm_adjMatrix p, pow_two,
      G.adjMatrix_mul_self_apply_self]
  have hcx : c x = 1 := by
    change (G.adjMatrix ℝ *ᵥ Pi.single p 1) x = 1
    rw [Matrix.mulVec_single_one]
    exact ite_eq_left hxp
  have hm4 : (A ^ 4) x x = (G.degree p : ℝ) + 2 * t + t ^ 2 := by
    rw [show A ^ 4 = (A ^ 2) ^ 2 from pow_mul A 2 2,
      symmetric_square_diagonal (A ^ 2) (G.isSymm_adjMatrix.pow 2), h2]
    simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, dotProduct_single, single_dotProduct, mul_one, hc, hcx]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, hcx, mul_one]
    ring
  have hm2 : (A ^ 2) x x = (G.degree x : ℝ) := by
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have hpN : p ∈ G.neighborFinset x := (G.mem_neighborFinset x p).mpr hxp
  have hcard := Finset.card_erase_add_one hpN
  rw [Finset.card_erase_of_mem hpN, G.card_neighborFinset_eq_degree] at hcard
  have hdegree : t + 1 = (G.degree x : ℝ) := by
    change ((G.degree x - 1 : ℕ) : ℝ) + 1 = (G.degree x : ℝ)
    exact_mod_cast hcard
  change (A ^ 4) x x - 5 * (A ^ 2) x x + 4 * (1 : Matrix V V ℝ) x x =
    (G.degree p : ℝ) + t ^ 2 - 3 * t - 1
  rw [hm4, hm2, Matrix.one_apply_eq, ← hdegree]
  ring
#print axioms Paper7IntroLocalQuartic.terminal_fan_quartic_diagonal

theorem integral_connected_small_terminal_fan_parent_ge_four
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (s : ℝ) (hs : s ∈ spec G) (hs2 : 2 < s)
    (x p : V) (hxp : G.Adj x p)
    (hx : G.degree x = 2 ∨ G.degree x = 3)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    4 ≤ G.degree p := by
  have hp := integral_connected_quartic_diagonal_pos G hG hI s hs hs2 x
  rw [terminal_fan_quartic_diagonal G x p hxp hleaf] at hp
  have hp3 : (3 : ℝ) < (G.degree p : ℝ) := by
    rcases hx with hx | hx
    · rw [hx] at hp
      norm_num at hp
      linarith
    · rw [hx] at hp
      norm_num at hp
      linarith
  have hpN : 3 < G.degree p := by exact_mod_cast hp3
  omega
#print axioms Paper7IntroLocalQuartic.integral_connected_small_terminal_fan_parent_ge_four

theorem integral_radius_three_small_terminal_fan_parent_ge_four
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (hthree : (integerSpectrum G).count 3 = 1)
    (x p : V) (hxp : G.Adj x p)
    (hx : G.degree x = 2 ∨ G.degree x = 3)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    4 ≤ G.degree p := by
  have hm : (3 : ℤ) ∈ integerSpectrum G := Multiset.count_pos.mp (by omega)
  have hs : (3 : ℝ) ∈ spec G := by
    rw [← integerSpectrum_cast G hI]
    exact Multiset.mem_map.mpr ⟨3, hm, by norm_num⟩
  exact integral_connected_small_terminal_fan_parent_ge_four
    G hG hI 3 hs (by norm_num) x p hxp hx hleaf
#print axioms Paper7IntroLocalQuartic.integral_radius_three_small_terminal_fan_parent_ge_four

end Paper7IntroLocalQuartic
