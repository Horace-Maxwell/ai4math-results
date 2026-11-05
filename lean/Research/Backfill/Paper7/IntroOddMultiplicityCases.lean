import Research.Backfill.Paper7.IntroOddPerronData

/-! Three necessary alternatives proved from the actual integer spectrum.
The radius-four alternative contains every multiplicity, including zero.
No root-profile alternative is an input hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroOddMultiplicity
open BackfillPaper7.Challenge Paper7OddIntegral

theorem radius_four_signed_cost (d : ℤ)
    (h : 16 + 9 * |d| + 4 * |-9 - 4 * d| + |14 + 5 * d| ≤ 42) : d = -2 := by
  by_contra hd
  have hc : d ≤ -3 ∨ -1 ≤ d := by omega
  rcases hc with hlo | hhi
  · have hd0 : d ≤ 0 := by omega
    have h2 : 0 ≤ -9 - 4 * d := by omega
    have h1 : 14 + 5 * d ≤ 0 := by omega
    rw [abs_of_nonpos hd0, abs_of_nonneg h2, abs_of_nonpos h1] at h
    omega
  · have h2 : -9 - 4 * d ≤ 0 := by omega
    have h1 : 0 ≤ 14 + 5 * d := by omega
    have hab : -d ≤ |d| := neg_le_abs d
    rw [abs_of_nonpos h2, abs_of_nonneg h1] at h
    omega
#print axioms Paper7IntroOddMultiplicity.radius_four_signed_cost

theorem intro21_odd_actual_multiplicity_cases
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Odd b) :
    Fintype.card V = 3 ∨
    ((integerSpectrum G).count 3 = 1 ∧ (integerSpectrum G).count (-3) = 0 ∧
      (integerSpectrum G).count 4 = 0 ∧ (integerSpectrum G).count (-4) = 0 ∧
      signedIntegerMultiplicity G 2 = -3 ∧ signedIntegerMultiplicity G 1 = 3) ∨
    (Fintype.card V = 21 ∧
      (integerSpectrum G).count 4 = 1 ∧ (integerSpectrum G).count (-4) = 0 ∧
      (integerSpectrum G).count 3 = 0 ∧ (integerSpectrum G).count (-3) = 2 ∧
      (integerSpectrum G).count 2 = 0 ∧ (integerSpectrum G).count (-2) = 1 ∧
      (integerSpectrum G).count 1 = 4 ∧ (integerSpectrum G).count (-1) = 0 ∧
      (integerSpectrum G).count 0 = 13) := by
  have htotal := intro21_multiplicity_total G b hG hI hn
  have htwo := intro21_paired_second_moment G b hG hI hn
  obtain ⟨hrel2, hrel1⟩ := intro21_signed_multiplicity_relations G b hG hI hn hb
  have hcost := intro21_signed_square_cost G b hG hI hn
  obtain ⟨R, hcases, hpos, hneg, hbound⟩ := intro21_odd_perron_integer_data G b hG hI hn hb
  rcases hcases with rfl | rfl | rfl
  · have hp3 := integerSpectrum_count_zero_above_bound G 2 3 hbound (by norm_num)
    have hm3 := integerSpectrum_count_zero_above_bound G 2 (-3) hbound (by norm_num)
    have hp4 := integerSpectrum_count_zero_above_bound G 2 4 hbound (by norm_num)
    have hm4 := integerSpectrum_count_zero_above_bound G 2 (-4) hbound (by norm_num)
    have hfirst := intro21_signed_first_moment G b hG hI hn
    dsimp only [pairedIntegerMultiplicity] at htotal htwo
    dsimp only [signedIntegerMultiplicity] at hfirst
    rw [hp3, hm3, hp4, hm4, hpos, hneg] at htotal htwo hfirst
    norm_num at htotal htwo hfirst
    exact Or.inl (by omega)
  · have hp4 := integerSpectrum_count_zero_above_bound G 3 4 hbound (by norm_num)
    have hm4 := integerSpectrum_count_zero_above_bound G 3 (-4) hbound (by norm_num)
    have hd3 : signedIntegerMultiplicity G 3 = 1 := by
      norm_num [signedIntegerMultiplicity, hpos, hneg]
    have hd4 : signedIntegerMultiplicity G 4 = 0 := by
      norm_num [signedIntegerMultiplicity, hp4, hm4]
    exact Or.inr (Or.inl ⟨hpos, hneg, hp4, hm4, by omega, by omega⟩)
  · have hd4 : signedIntegerMultiplicity G 4 = 1 := by
      norm_num [signedIntegerMultiplicity, hpos, hneg]
    have hd2 : signedIntegerMultiplicity G 2 = -9 - 4 * signedIntegerMultiplicity G 3 := by
      omega
    have hd1 : signedIntegerMultiplicity G 1 = 14 + 5 * signedIntegerMultiplicity G 3 := by
      omega
    have hd3 : signedIntegerMultiplicity G 3 = -2 := by
      apply radius_four_signed_cost
      rw [hd1, hd2, hd4] at hcost
      norm_num at hcost
      linarith
    have hv2 : signedIntegerMultiplicity G 2 = -1 := by omega
    have hv1 : signedIntegerMultiplicity G 1 = 4 := by omega
    dsimp only [signedIntegerMultiplicity] at hd3 hv2 hv1
    dsimp only [pairedIntegerMultiplicity] at htotal htwo
    rw [hpos, hneg] at htotal htwo
    norm_num at htotal htwo
    refine Or.inr (Or.inr ⟨?_, hpos, hneg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) <;> omega
#print axioms Paper7IntroOddMultiplicity.intro21_odd_actual_multiplicity_cases

end Paper7IntroOddMultiplicity
