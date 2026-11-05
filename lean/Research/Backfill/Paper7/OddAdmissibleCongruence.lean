import Research.Backfill.Paper7.LegacyCandidates

/-! Congruence obstructions for the literal finite spectral feature contract.
These helpers do not assert the entire LegacySpectrumEmptyCells contract. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Paper7FeatureEmpty
open BackfillPaper7.Challenge.Legacy

theorem admissible_top_dvd (cyc : Bool) (b N : ℕ) (s : SpectralCounts)
    (hb : Odd b) (h3 : 3 ≤ b) (d : ℤ)
    (hv : ∀ i : Fin 8, d ∣ (value i : ℤ) ^ b - value i)
    (hs : Admissible cyc b N s) : d ∣ 2 * (b : ℤ) := by
  have hm := hs.1.2.2 hb b hb h3 (le_refl b)
  have he : (∑ i : Fin 8, ((s.1 i).val - (s.2 i).val : ℤ) *
      ((value i : ℤ) ^ b - value i)) = 2 * (b : ℤ) := by
    simpa only [ite_true, Nat.cast_mul, Nat.cast_ofNat] using hm
  rw [← he]
  exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hv i) _)
#print axioms Paper7FeatureEmpty.admissible_top_dvd

theorem admissible_false_of_top_congruence (cyc : Bool) (b N : ℕ)
    (hb : Odd b) (h3 : 3 ≤ b) (d : ℤ)
    (hv : ∀ i : Fin 8, d ∣ (value i : ℤ) ^ b - value i)
    (hnot : ¬ d ∣ 2 * (b : ℤ)) (s : SpectralCounts) :
    ¬ Admissible cyc b N s := by
  intro hs
  exact hnot (admissible_top_dvd cyc b N s hb h3 d hv hs)
#print axioms Paper7FeatureEmpty.admissible_false_of_top_congruence

theorem five_odd_cells_empty (cyc : Bool) (N b : ℕ)
    (hb : b ∈ ({5, 7, 9, 11, 13} : Finset ℕ)) :
    {s | Admissible cyc b N s} = ∅ := by
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact admissible_false_of_top_congruence cyc 5 N (by norm_num) (by norm_num) 3
      (by intro i; fin_cases i <;> norm_num [value]) (by norm_num) s
  · exact admissible_false_of_top_congruence cyc 7 N (by norm_num) (by norm_num) 3
      (by intro i; fin_cases i <;> norm_num [value]) (by norm_num) s
  · exact admissible_false_of_top_congruence cyc 9 N (by norm_num) (by norm_num) 5
      (by intro i; fin_cases i <;> norm_num [value]) (by norm_num) s
  · exact admissible_false_of_top_congruence cyc 11 N (by norm_num) (by norm_num) 3
      (by intro i; fin_cases i <;> norm_num [value]) (by norm_num) s
  · exact admissible_false_of_top_congruence cyc 13 N (by norm_num) (by norm_num) 3
      (by intro i; fin_cases i <;> norm_num [value]) (by norm_num) s
#print axioms Paper7FeatureEmpty.five_odd_cells_empty

end Paper7FeatureEmpty
