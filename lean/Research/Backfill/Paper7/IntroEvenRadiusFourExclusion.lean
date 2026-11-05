import Research.Backfill.Paper7.IntroLeafInertia

/-! Complete candidate exclusion of Perron four in the original arbitrary
even unicyclic order-21 range. The final graph statements have no profile,
nonbranching, Sun, or auxiliary numerical premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroFour
open BackfillPaper7.Challenge Paper7OddIntegral Paper7Unicyclic
open Paper7IntroEven Paper7IntroOddMultiplicity

theorem intro21_even_no_top_four
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (hfour : (integerSpectrum G).count 4 = 1) : False := by
  have hsecond := intro21_even_second_moment G b hG hI hn hb
  have hbranch := intro21_even_branch_moment G b hG hI hn hb
  have hthree : (integerSpectrum G).count 3 = 0 := by
    rw [hfour] at hsecond
    omega
  rw [hthree, hfour] at hsecond hbranch
  norm_num at hsecond hbranch
  have hv : (integerSpectrum G).count 2 = 0 ∨ (integerSpectrum G).count 2 = 1 := by omega
  have hcycles : cycleCount G 4 ≤ 1 := by
    rw [unicyclic_cycleCount hG 4]
    split_ifs <;> omega
  have hnZ : (Fintype.card V : ℤ) ≤ 21 := by exact_mod_cast hn
  have hcZ : (cycleCount G 4 : ℤ) ≤ 1 := by exact_mod_cast hcycles
  rcases hv with hv | hv
  · have hinertia := unicyclic_positive_inertia_add_leaves_le_card G b hG
    rw [intro21_positive_inertia_actual_counts G b hG hI hn,
      hthree, hfour, hv] at hinertia
    rw [hv] at hsecond hbranch
    norm_num at hinertia hsecond hbranch
    have hleaf : (leafVerts G).card ≤ 15 := by omega
    have hD := intro21_branch_mass_le_188_of_leaves_le_fifteen G b hG hI hn hleaf
    linarith
  · have hleafCycle := unicyclic_leaf_card_add_cycle_le G b hG
    have hbFour : 4 ≤ b := by
      have hthree := unicyclic_three_le hG
      obtain ⟨k, hk⟩ := hb
      omega
    have hleaf : (leafVerts G).card ≤ 17 := by omega
    have hD := intro21_branch_mass_le_202_of_leaves_le_seventeen G b hG hI hn hleaf
    rw [hv] at hbranch
    norm_num at hbranch
    linarith
#print axioms Paper7IntroFour.intro21_even_no_top_four

theorem intro21_even_count_four_eq_zero
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b) : (integerSpectrum G).count 4 = 0 := by
  obtain ⟨R, hR, htop, hbound⟩ := intro21_perron_integer_data G b hG hI hn
  rcases hR with rfl | rfl | rfl
  · exact integerSpectrum_count_zero_above_bound G 2 4 hbound (by norm_num)
  · exact integerSpectrum_count_zero_above_bound G 3 4 hbound (by norm_num)
  · exact (intro21_even_no_top_four G b hG hI hn hb htop).elim
#print axioms Paper7IntroFour.intro21_even_count_four_eq_zero

theorem intro21_even_integer_spectrum_abs_le_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b) (z : ℤ) (hz : z ∈ integerSpectrum G) :
    |z| ≤ 3 := by
  have hwin := intro21_integerSpectrum_bounds G b hG hI hn z hz
  have hp := intro21_even_count_four_eq_zero G b hG hI hn hb
  have hm : (integerSpectrum G).count (-4) = 0 :=
    (even_unicyclic_integer_count_neg G b hG hI hb 4).symm.trans hp
  have hzp : z ≠ 4 := by
    intro he
    exact (Multiset.count_eq_zero.mp hp) (he ▸ hz)
  have hzm : z ≠ -4 := by
    intro he
    exact (Multiset.count_eq_zero.mp hm) (he ▸ hz)
  exact abs_le.mpr ⟨by omega, by omega⟩
#print axioms Paper7IntroFour.intro21_even_integer_spectrum_abs_le_three

theorem intro21_even_spectrum_abs_le_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b) (x : ℝ) (hx : x ∈ spec G) : |x| ≤ 3 := by
  rw [← integerSpectrum_cast G hI] at hx
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
  have h := intro21_even_integer_spectrum_abs_le_three G b hG hI hn hb z hz
  exact_mod_cast h
#print axioms Paper7IntroFour.intro21_even_spectrum_abs_le_three

theorem intro21_even_degree_le_eight
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b) (i : V) : G.degree i ≤ 8 := by
  have h := unicyclic_degree_lt_spectral_bound_sq G b hG 3 (by norm_num) (by
    intro x hx
    exact (le_abs_self x).trans (intro21_even_spectrum_abs_le_three G b hG hI hn hb x hx)) i
  norm_num at h
  have hi : G.degree i < 9 := by exact_mod_cast h
  omega
#print axioms Paper7IntroFour.intro21_even_degree_le_eight

end Paper7IntroFour
