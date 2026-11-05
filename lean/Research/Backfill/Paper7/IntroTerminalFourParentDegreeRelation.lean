import Research.Backfill.Paper7.IntroTerminalFourParentNorm

/-! A degree relation under explicit, actual leaf hypotheses at the parent.
This does not derive those hypotheses from an outside-component statement. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroTerminalFourRemote
open Matrix SimpleGraph BackfillPaper7.Challenge
open Paper7IntroLocalQuartic

theorem parent_two_nonleaf_square_column
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p x c : V) (hpx : G.Adj p x) (hpc : G.Adj p c) (hxc : x ≠ c)
    (hleaf : ∀ j, G.Adj p j → j ≠ x → j ≠ c → G.degree j = 1) :
    (G.adjMatrix ℝ) ^ 2 *ᵥ Pi.single p 1 =
      G.adjMatrix ℝ *ᵥ Pi.single x 1 + G.adjMatrix ℝ *ᵥ Pi.single c 1 +
        (((G.degree p - 2 : ℕ) : ℝ)) • Pi.single p 1 := by
  let E := ((G.neighborFinset p).erase x).erase c
  have hxN : x ∈ G.neighborFinset p := (G.mem_neighborFinset p x).mpr hpx
  have hcN : c ∈ (G.neighborFinset p).erase x :=
    Finset.mem_erase.mpr ⟨hxc.symm, (G.mem_neighborFinset p c).mpr hpc⟩
  have hEcard : E.card = G.degree p - 2 := by
    rw [Finset.card_erase_of_mem hcN, Finset.card_erase_of_mem hxN,
      G.card_neighborFinset_eq_degree]
    omega
  have hcol (k : V) (hk : k ∈ E) (j : V) :
      G.adjMatrix ℝ j k = (Pi.single p (1 : ℝ) : V → ℝ) j := by
    have hkc := (Finset.mem_erase.mp hk).1
    have hkx := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hpk : G.Adj p k := (G.mem_neighborFinset p k).mp
      (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2
    have hd := hleaf k hpk hkx hkc
    obtain ⟨_t, _hkt, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd
    have hadj : G.Adj j k ↔ j = p := by
      constructor
      · intro hjk
        exact (huniq j hjk.symm).trans (huniq p hpk.symm).symm
      · intro hjp
        exact hjp.symm ▸ hpk
    change (if G.Adj j k then (1 : ℝ) else 0) = _
    by_cases hjp : j = p
    · subst j
      rw [ite_eq_left hpk, Pi.single_eq_same]
    · rw [ite_eq_right (fun h => hjp (hadj.mp h)),
        Pi.single_eq_of_ne (M := fun _ : V => ℝ) hjp (1 : ℝ)]
  funext j
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
    pow_two]
  change (G.adjMatrix ℝ * G.adjMatrix ℝ) j p =
    G.adjMatrix ℝ j x + G.adjMatrix ℝ j c +
      ((G.degree p - 2 : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : V → ℝ) j
  rw [G.mul_adjMatrix_apply]
  rw [← Finset.add_sum_erase (G.neighborFinset p) (fun k => G.adjMatrix ℝ j k) hxN,
    ← Finset.add_sum_erase ((G.neighborFinset p).erase x)
      (fun k => G.adjMatrix ℝ j k) hcN]
  have hs : (∑ k ∈ E, G.adjMatrix ℝ j k) =
      ∑ _k ∈ E, (Pi.single p (1 : ℝ) : V → ℝ) j :=
    Finset.sum_congr rfl (fun k hk => hcol k hk j)
  rw [hs, Finset.sum_const, nsmul_eq_mul, hEcard]
  ring
#print axioms Paper7IntroTerminalFourRemote.parent_two_nonleaf_square_column

theorem integral_terminal_four_parent_other_degree_relation
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (x p c : V) (hxp : G.Adj x p) (hpc : G.Adj p c) (hxc : x ≠ c)
    (hx : G.degree x = 4)
    (hxleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1)
    (hpleaf : ∀ j, G.Adj p j → j ≠ x → j ≠ c → G.degree j = 1) :
    (G.degree c : ℝ) = -(G.degree p : ℝ) ^ 2 + 8 * (G.degree p : ℝ) - 6 := by
  let A := G.adjMatrix ℝ
  let ex : V → ℝ := Pi.single x 1
  let ep : V → ℝ := Pi.single p 1
  let ec : V → ℝ := Pi.single c 1
  let u : V → ℝ := A *ᵥ ep - ex
  let k : ℝ := (G.degree p - 2 : ℕ)
  have hxN : x ∈ G.neighborFinset p := (G.mem_neighborFinset p x).mpr hxp.symm
  have hcN : c ∈ (G.neighborFinset p).erase x :=
    Finset.mem_erase.mpr ⟨hxc.symm, (G.mem_neighborFinset p c).mpr hpc⟩
  have hd2 : 2 ≤ G.degree p := by
    have hpos := Finset.card_pos.mpr ⟨c, hcN⟩
    rw [Finset.card_erase_of_mem hxN, G.card_neighborFinset_eq_degree] at hpos
    omega
  have hk : k = (G.degree p : ℝ) - 2 := by
    dsimp only [k]
    rw [Nat.cast_sub hd2]
    norm_num
  have hcol : A ^ 2 *ᵥ ep = A *ᵥ ex + A *ᵥ ec + k • ep :=
    parent_two_nonleaf_square_column G p x c hxp.symm hpc hxc hpleaf
  have hAu : A *ᵥ u = A *ᵥ ec + k • ep := by
    change A *ᵥ (A *ᵥ ep - ex) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← pow_two, hcol]
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hc : (A *ᵥ ec) ⬝ᵥ (A *ᵥ ec) = (G.degree c : ℝ) := by
    rw [← symmetric_square_diagonal A G.isSymm_adjMatrix c, pow_two,
      G.adjMatrix_mul_self_apply_self]
  have hcp : (A *ᵥ ec) p = 1 := by
    change (G.adjMatrix ℝ *ᵥ Pi.single c 1) p = 1
    rw [Matrix.mulVec_single_one]
    exact ite_eq_left hpc
  have hnorm : (A *ᵥ u) ⬝ᵥ (A *ᵥ u) = (G.degree c : ℝ) + 2 * k + k ^ 2 := by
    rw [hAu]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, ep, single_dotProduct, dotProduct_single, mul_one, hc, hcp]
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, hcp]
    ring
  have hn := (integral_terminal_four_parent_vector_norm G hI hbound x p hxp hx hxleaf).2
  change (A *ᵥ u) ⬝ᵥ (A *ᵥ u) = 6 * ((G.degree p : ℝ) - 1) at hn
  rw [hnorm, hk] at hn
  nlinarith
#print axioms Paper7IntroTerminalFourRemote.integral_terminal_four_parent_other_degree_relation

end Paper7IntroTerminalFourRemote
