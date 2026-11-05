import Research.Backfill.Paper7.IntroEvenDegreeMoments
import Research.Backfill.Paper7.IntroOddPerronData
import Research.Backfill.Paper7.UnicyclicBareCycleIso

/-! Exact alternatives from the actual graph. The remaining natural parameters
are actual multiplicities, and their moment budgets are derived conclusions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroEven
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7OddIntegral
open Paper7Unicyclic Paper7IntroGeneral Paper7IntroOddMultiplicity Paper7Admissible

theorem unicyclic_cycle_le_card
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) : b ≤ Fintype.card V := by
  obtain ⟨s, ⟨r, w, hw, hlen, _hs⟩, _hu⟩ := hG.2
  have h := hw.isTrail.length_le_card_edgeFinset
  rw [hlen, unicyclic_card_edges G hG] at h
  exact h
#print axioms Paper7IntroEven.unicyclic_cycle_le_card

theorem intro21_perron_integer_data
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) :
    ∃ R : ℤ, (R = 2 ∨ R = 3 ∨ R = 4) ∧
      (integerSpectrum G).count R = 1 ∧ ∀ z ∈ integerSpectrum G, |z| ≤ R := by
  let : Nonempty V := hG.1.nonempty
  obtain ⟨r, hr, _v, _hv, _hvnorm, _hve, _hr0, hsimple, hupper, hdom⟩ :=
    connected_perron G hG.1
  have hu := hupper (fun _ : V => 1)
  have honenorm : (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) =
      (Fintype.card V : ℝ) := by simp [dotProduct]
  rw [adjacency_quadratic_ones, unicyclic_card_edges G hG, honenorm] at hu
  have hnpos : 0 < (Fintype.card V : ℝ) := by
    have hthree := unicyclic_card_ge_three G hG
    exact_mod_cast (show 0 < Fintype.card V by omega)
  have hr2 : 2 ≤ r := (mul_le_mul_iff_left₀ hnpos).mp hu
  obtain ⟨R, hR, _hlo, hhi⟩ := integral_unicyclic21_spectrum_window G hG hI hn r hr
  have hR2 : (2 : ℤ) ≤ R := by
    rw [hR] at hr2
    exact_mod_cast hr2
  refine ⟨R, by omega, ?_, ?_⟩
  · rw [integerSpectrum_count G hI]
    simpa only [hR] using hsimple
  · intro z hz
    have hzr : (z : ℝ) ∈ spec G := by
      rw [← integerSpectrum_cast G hI]
      exact Multiset.mem_map.mpr ⟨z, hz, rfl⟩
    have hd := hdom z hzr
    rw [hR] at hd
    exact_mod_cast hd
#print axioms Paper7IntroEven.intro21_perron_integer_data

theorem intro21_even_actual_spectral_alternatives
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b) :
    Nonempty (G ≃g cycleGraph 4) ∨ Nonempty (G ≃g cycleGraph 6) ∨
    (∃ a u v : ℕ, a = (integerSpectrum G).count 0 ∧
      u = (integerSpectrum G).count 1 ∧ v = (integerSpectrum G).count 2 ∧
      Fintype.card V = 9 + u + 4 * v ∧ a + u = 7 + 2 * v ∧ u + 4 * v ≤ 12 ∧
      (integerSpectrum G).count 3 = 1 ∧ (integerSpectrum G).count 4 = 0 ∧
      degreeDeviation G + 2 * (Fintype.card V : ℤ) + 4 * (cycleCount G 4 : ℤ) =
        72 + 12 * (v : ℤ)) ∨
    (∃ a u v : ℕ, a = (integerSpectrum G).count 0 ∧
      u = (integerSpectrum G).count 1 ∧ v = (integerSpectrum G).count 2 ∧
      Fintype.card V = 16 + u + 4 * v ∧ a + u = 14 + 2 * v ∧ u + 4 * v ≤ 5 ∧
      (integerSpectrum G).count 3 = 0 ∧ (integerSpectrum G).count 4 = 1 ∧
      degreeDeviation G + 2 * (Fintype.card V : ℤ) + 4 * (cycleCount G 4 : ℤ) =
        240 + 12 * (v : ℤ)) := by
  have hcard := intro21_even_multiplicity_card G b hG hI hn hb
  have hsecond := intro21_even_second_moment G b hG hI hn hb
  have hbranch := intro21_even_branch_moment G b hG hI hn hb
  obtain ⟨R, hR, htop, hbound⟩ := intro21_perron_integer_data G b hG hI hn
  rcases hR with rfl | rfl | rfl
  · have h3 := integerSpectrum_count_zero_above_bound G 2 3 hbound (by norm_num)
    have h4 := integerSpectrum_count_zero_above_bound G 2 4 hbound (by norm_num)
    rw [htop, h3, h4] at hbranch
    norm_num at hbranch
    have hnonneg := degreeDeviation_nonneg G
    have hbcard := unicyclic_cycle_le_card G b hG
    rw [unicyclic_cycleCount hG 4] at hbranch
    by_cases hb4 : b = 4
    · subst b
      norm_num at hbranch
      have hn4 : Fintype.card V = 4 := by omega
      exact Or.inl (Paper7UnicyclicStructure.unicyclic_card_eq_cycle_iso G 4 hG hn4)
    · have hfour : 4 ≠ b := Ne.symm hb4
      simp only [ite_eq_right hfour, Nat.cast_zero, mul_zero, add_zero] at hbranch
      have hbthree := unicyclic_three_le hG
      obtain ⟨k, hk⟩ := hb
      have hb6 : 6 ≤ b := by omega
      have hn6 : Fintype.card V = 6 := by omega
      have hbEq : b = 6 := by omega
      rw [hbEq] at hG
      exact Or.inr (Or.inl (Paper7UnicyclicStructure.unicyclic_card_eq_cycle_iso G 6 hG hn6))
  · have h4 := integerSpectrum_count_zero_above_bound G 3 4 hbound (by norm_num)
    rw [htop, h4] at hcard hsecond hbranch
    norm_num at hcard hsecond hbranch
    refine Or.inr (Or.inr (Or.inl ⟨(integerSpectrum G).count 0,
      (integerSpectrum G).count 1, (integerSpectrum G).count 2,
      rfl, rfl, rfl, ?_, ?_, ?_, htop, h4, ?_⟩)) <;> omega
  · have h3 : (integerSpectrum G).count 3 = 0 := by
      rw [htop] at hsecond
      omega
    rw [h3, htop] at hcard hsecond hbranch
    norm_num at hcard hsecond hbranch
    refine Or.inr (Or.inr (Or.inr ⟨(integerSpectrum G).count 0,
      (integerSpectrum G).count 1, (integerSpectrum G).count 2,
      rfl, rfl, rfl, ?_, ?_, ?_, h3, htop, ?_⟩)) <;> omega
#print axioms Paper7IntroEven.intro21_even_actual_spectral_alternatives

end Paper7IntroEven
