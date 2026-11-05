import Research.Backfill.Paper7.LegacyEnumeration
import Research.Backfill.Paper7.ReportedALeafBound

/-! Empty B version-3 cells from the literal feature/count guards alone.
No spectrum realization, integrality, search completeness or historical run
outcome is assumed. The other original B guards may remain unused. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Paper7PruningEmpty
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

/-- Only values 2 and 3 can contribute less than sixteen per positive count;
their multiplicities are each at most two. -/
theorem even_feature_sixteen_bound (b : ℕ) (s : SpectralCounts) (he : Even b) :
    16 * (posCard s : ℤ) ≤ s2 b s + 38 := by
  have hterm (i : Fin 8) :
      16 * ((s.1 i).val : ℤ) ≤ ((s.1 i).val : ℤ) * (value i : ℤ)^2 +
        (if i = 0 then 24 else 0) + (if i = 1 then 14 else 0) := by
    by_cases h0 : i = 0
    · subst i
      have hc : ((s.1 (0 : Fin 8)).val : ℤ) ≤ 2 := by
        exact_mod_cast (show (s.1 (0 : Fin 8)).val ≤ 2 by omega)
      norm_num [value]
      omega
    · by_cases h1 : i = 1
      · subst i
        have hc : ((s.1 (1 : Fin 8)).val : ℤ) ≤ 2 := by
          exact_mod_cast (show (s.1 (1 : Fin 8)).val ≤ 2 by omega)
        norm_num [value]
        omega
      · have hi0 : i.val ≠ 0 := by intro h; exact h0 (Fin.ext h)
        have hi1 : i.val ≠ 1 := by intro h; exact h1 (Fin.ext h)
        have hv : (4 : ℤ) ≤ value i := by
          exact_mod_cast (show 4 ≤ value i by unfold value; omega)
        have hv2 : (16 : ℤ) ≤ (value i : ℤ)^2 := by nlinarith
        have hc : (0 : ℤ) ≤ (s.1 i).val := by positivity
        simp only [ite_eq_right h0, ite_eq_right h1, add_zero]
        calc
          16 * ((s.1 i).val : ℤ) = ((s.1 i).val : ℤ) * 16 := mul_comm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left hv2 hc
  calc
    16 * (posCard s : ℤ) = ∑ i : Fin 8, (16 : ℤ) * ((s.1 i).val : ℤ) := by
      rw [posCard, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ i : Fin 8, (((s.1 i).val : ℤ) * (value i : ℤ)^2 +
        (if i = 0 then 24 else 0) + (if i = 1 then 14 else 0)) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = s2 b s + 38 := by simp [s2, he, Finset.sum_add_distrib, add_assoc]
#print axioms Paper7PruningEmpty.even_feature_sixteen_bound

theorem even_filtered_five_feature (b : ℕ) (s : SpectralCounts) (he : Even b)
    (hcycle : 5 ≤ cyclicPositive b) (hs : Admissible true b 42 s) :
    posCard s = 5 ∧ s2 b s = 42 := by
  have hlow : 5 ≤ posCard s := hcycle.trans (hs.2 rfl).1
  have hhigh := Paper7CRTEnvelope.admissible_even_42_posCard_le_five b s he hs
  have hcard : posCard s = 5 := by omega
  have hupper : s2 b s ≤ 42 := by
    simpa only [he, ite_true, Nat.cast_ofNat] using hs.1.2.1
  have hlower := even_feature_sixteen_bound b s he
  rw [hcard] at hlower
  exact ⟨hcard, by omega⟩
#print axioms Paper7PruningEmpty.even_filtered_five_feature

/-- This is a contradiction between the original Budget and MomentPass
predicates, without treating a feature assignment as an integral graph. -/
theorem counted_even_moment_false (b : ℕ) (hb : 11 ≤ b) (he : Even b)
    (hcycle : 5 ≤ cyclicPositive b) (x : PQ b) (hbudget : Budget b 42 x)
    (hpass : MomentPass true true true b 42 x) : False := by
  obtain ⟨s, hs, _hm4, _hs2, _hload, hcount⟩ := hpass
  obtain ⟨hcard, hS2⟩ := even_filtered_five_feature b s he hcycle hs
  have hc := (hcount rfl he).2
  rw [hS2, hcard] at hc
  have hp : pSum x ≤ 31 := by
    have hn := hbudget.2
    unfold weight at hn
    omega
  have hmax : max (pSum x) 2 ≤ 31 := max_le hp (by omega)
  have hn : (b : ℤ) + (weight x : ℤ) ≤ 42 := by exact_mod_cast hbudget.2
  have hmaxInt : ((max (pSum x) 2 : ℕ) : ℤ) ≤ 31 := by exact_mod_cast hmax
  omega
#print axioms Paper7PruningEmpty.counted_even_moment_false

theorem cyclic_positive_fourteen : cyclicPositive 14 = 5 := by
  decide +kernel
#print axioms Paper7PruningEmpty.cyclic_positive_fourteen

theorem cyclic_positive_eighteen : cyclicPositive 18 = 5 := by
  decide +kernel
#print axioms Paper7PruningEmpty.cyclic_positive_eighteen

theorem pruning_b3_fourteen_empty : CandB3 14 42 = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  change BReaches true true true true 14 42 x at hx
  exact counted_even_moment_false 14 (by omega) (by decide)
    (le_of_eq cyclic_positive_fourteen.symm) x hx.1 hx.2.1
#print axioms Paper7PruningEmpty.pruning_b3_fourteen_empty

theorem pruning_b3_eighteen_empty : CandB3 18 42 = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  change BReaches true true true true 18 42 x at hx
  exact counted_even_moment_false 18 (by omega) (by decide)
    (le_of_eq cyclic_positive_eighteen.symm) x hx.1 hx.2.1
#print axioms Paper7PruningEmpty.pruning_b3_eighteen_empty

end Paper7PruningEmpty
