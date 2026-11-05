import Research.Backfill.Paper7.IntroEvenRadiusFourExclusion

/-! Every actual radius-three graph in the original even order-21 range has a high vertex. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroHighVertex
open SimpleGraph BackfillPaper7.Challenge Paper7Unicyclic Paper7OddIntegral
open Paper7IntroFour Paper7IntroEven

theorem unicyclic_degree_cap_four_branch_mass
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hcap : ∀ i, G.degree i ≤ 4) :
    degreeDeviation G ≤ 3 * ((leafVerts G).card : ℤ) := by
  obtain ⟨hexcess, hmass⟩ := unicyclic_leaf_excess_identities G b hG
  have hsq : (∑ i ∈ nonleafVerts G, ((G.degree i : ℤ) - 2) ^ 2) ≤
      2 * (∑ i ∈ nonleafVerts G, ((G.degree i : ℤ) - 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hlo : 2 ≤ G.degree i := (Finset.mem_filter.mp hi).2
    have hhi := hcap i
    have hloZ : (2 : ℤ) ≤ G.degree i := by exact_mod_cast hlo
    have hhiZ : (G.degree i : ℤ) ≤ 4 := by exact_mod_cast hhi
    have hp := mul_nonneg (show (0 : ℤ) ≤ (G.degree i : ℤ) - 2 by omega)
      (show (0 : ℤ) ≤ 4 - (G.degree i : ℤ) by omega)
    nlinarith
  rw [hexcess] at hsq
  linarith
#print axioms Paper7IntroHighVertex.unicyclic_degree_cap_four_branch_mass

theorem intro21_even_radius_three_exists_degree_ge_five
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (hthree : (integerSpectrum G).count 3 = 1) : ∃ i, 5 ≤ G.degree i := by
  by_contra hno
  have hcap : ∀ i, G.degree i ≤ 4 := by
    intro i
    have hi : ¬5 ≤ G.degree i := fun h => hno ⟨i, h⟩
    omega
  have hmass := unicyclic_degree_cap_four_branch_mass G b hG hcap
  have hfour := intro21_even_count_four_eq_zero G b hG hI hn hb
  have hsecond := intro21_even_second_moment G b hG hI hn hb
  have hbranch := intro21_even_branch_moment G b hG hI hn hb
  have hleaf := unicyclic_positive_inertia_add_leaves_le_card G b hG
  rw [intro21_positive_inertia_actual_counts G b hG hI hn] at hleaf
  rw [hthree, hfour] at hsecond hbranch hleaf
  norm_num at hsecond hbranch hleaf
  have hcycles : cycleCount G 4 ≤ 1 := by
    rw [unicyclic_cycleCount hG 4]
    split_ifs <;> omega
  have hsecondZ : ((integerSpectrum G).count 1 : ℤ) +
      4 * ((integerSpectrum G).count 2 : ℤ) + 9 = (Fintype.card V : ℤ) := by
    exact_mod_cast hsecond
  have hleafZ : ((integerSpectrum G).count 1 : ℤ) +
      ((integerSpectrum G).count 2 : ℤ) + 1 + ((leafVerts G).card : ℤ) ≤
        (Fintype.card V : ℤ) := by
    exact_mod_cast hleaf
  have hnZ : (Fintype.card V : ℤ) ≤ 21 := by exact_mod_cast hn
  have hcZ : (cycleCount G 4 : ℤ) ≤ 1 := by exact_mod_cast hcycles
  have hvZ : (0 : ℤ) ≤ (integerSpectrum G).count 2 := by exact_mod_cast Nat.zero_le _
  linarith
#print axioms Paper7IntroHighVertex.intro21_even_radius_three_exists_degree_ge_five

theorem intro21_even_cycle_or_high_vertex
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b) :
    Nonempty (G ≃g cycleGraph 4) ∨ Nonempty (G ≃g cycleGraph 6) ∨
      ∃ i, 5 ≤ G.degree i := by
  rcases intro21_even_actual_spectral_alternatives G b hG hI hn hb with
    hfour | hsix | hthree | htop
  · exact Or.inl hfour
  · exact Or.inr (Or.inl hsix)
  · obtain ⟨a, u, v, _ha, _hu, _hv, _hn, _haeq, _hbudget, hthree, _hfour, _hD⟩ := hthree
    exact Or.inr (Or.inr
      (intro21_even_radius_three_exists_degree_ge_five G b hG hI hn hb hthree))
  · obtain ⟨a, u, v, _ha, _hu, _hv, _hn, _haeq, _hbudget, _hthree, hfour, _hD⟩ := htop
    exact (intro21_even_no_top_four G b hG hI hn hb hfour).elim
#print axioms Paper7IntroHighVertex.intro21_even_cycle_or_high_vertex

end Paper7IntroHighVertex
