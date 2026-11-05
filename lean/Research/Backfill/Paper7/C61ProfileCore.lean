import Research.Backfill.Paper7.C61SpectralBounds
import Research.Backfill.Paper7.BoundedSpectralSums
import Research.Backfill.Paper7.Lemma24

/-! Source-only. The imported C61SpectralBounds chain is pending, while the
general spectrum and Perron dependencies are selected from real producers. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Profile
open BackfillPaper7.Challenge
open scoped BigOperators Classical

def value (i : Fin 5) : ℕ := i.val + 2
#print axioms Paper7C61Profile.value

def card (m : Fin 5 → Fin 3) : ℕ := ∑ i, (m i).val
#print axioms Paper7C61Profile.card

def square (m : Fin 5 → Fin 3) : ℕ := ∑ i, (m i).val * value i ^ 2
#print axioms Paper7C61Profile.square

def actual (p q : Fin 6 → ℕ) : Fin 5 → Fin 3 := fun i =>
  ⟨(Bplus (SG 6 p q)).count (value i : ℝ), Nat.lt_succ_of_le
    (Paper7Admissible.bplus_count_le_two 6 p q (by decide) (value i))⟩
#print axioms Paper7C61Profile.actual

theorem value_lower (i : Fin 5) : (2 : ℝ) ≤ value i := by
  have h : 2 ≤ value i := by unfold value; omega
  exact_mod_cast h
#print axioms Paper7C61Profile.value_lower

theorem value_injective : Function.Injective (fun i : Fin 5 => (value i : ℝ)) := by
  intro i j hij
  change (value i : ℝ) = (value j : ℝ) at hij
  have h : value i = value j := by exact_mod_cast hij
  apply Fin.ext
  unfold value at h
  omega
#print axioms Paper7C61Profile.value_injective

theorem actual_eq_mult (p q : Fin 6 → ℕ) (i : Fin 5) :
    (actual p q i).val = mult (SG 6 p q) (value i) := by
  exact Multiset.count_filter_of_pos (value_lower i)
#print axioms Paper7C61Profile.actual_eq_mult

theorem value_rep (x : ℝ) (hx : ∃ z : ℤ, x = z) (h2 : 2 ≤ x) (h6 : x ≤ 6) :
    ∃ i : Fin 5, (value i : ℝ) = x := by
  obtain ⟨z, hz⟩ := hx
  have hz2 : (2 : ℤ) ≤ z := by rw [hz] at h2; exact_mod_cast h2
  have hz6 : z ≤ (6 : ℤ) := by rw [hz] at h6; exact_mod_cast h6
  have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
  let i : Fin 5 := ⟨z.toNat - 2, by omega⟩
  have hi : value i = z.toNat := by dsimp [value, i]; omega
  refine ⟨i, ?_⟩
  rw [hi]
  have hc : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hzn
  exact hc.trans hz.symm
#print axioms Paper7C61Profile.value_rep

theorem bplus_covered (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) :
    ∀ x ∈ Bplus (SG 6 p q), ∃ i : Fin 5, (value i : ℝ) = x := by
  intro x hx
  have h := Multiset.mem_filter.mp hx
  exact value_rep x (Paper7Moments.integral_spec_entry (SG 6 p q) hG x h.1) h.2
    (Paper7C61Classification.bplus_entry_le_six p q hn hG x hx)
#print axioms Paper7C61Profile.bplus_covered

theorem actual_card (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : card (actual p q) = (Bplus (SG 6 p q)).card := by
  exact (Paper7PruningSpectrum.finite_count_card (Bplus (SG 6 p q))
    (fun i : Fin 5 => (value i : ℝ)) value_injective (bplus_covered p q hn hG)).symm
#print axioms Paper7C61Profile.actual_card

theorem bplus_sum (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (f : ℝ → ℝ) :
    ((Bplus (SG 6 p q)).map f).sum =
      ∑ i, ((actual p q i).val : ℝ) * f (value i) := by
  have h := Paper7PruningSpectrum.finite_count_sum (Bplus (SG 6 p q))
    (fun i : Fin 5 => (value i : ℝ)) value_injective (bplus_covered p q hn hG) f
  simpa only [actual, nsmul_eq_mul] using h
#print axioms Paper7C61Profile.bplus_sum

theorem actual_square (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : (square (actual p q) : ℝ) = S2 (SG 6 p q) := by
  have h := bplus_sum p q hn hG (fun x => x ^ 2)
  simpa only [square, S2, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using h.symm
#print axioms Paper7C61Profile.actual_square

def Admissible (m : Fin 5 → Fin 3) : Prop :=
  card m ≤ 5 ∧ square m ≤ 42 ∧
    ∃ r : Fin 5, 3 ≤ value r ∧ (m r).val = 1 ∧
      ∀ i, r.val < i.val → (m i).val = 0
#print axioms Paper7C61Profile.Admissible

theorem actual_admissible (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : Admissible (actual p q) := by
  have hL := Paper7Admissible.check_Lemma24 6 p q (by decide) hp hG
  obtain ⟨r, hr, hsimple, hr3, hmax⟩ := hL.1
  obtain ⟨i, hi⟩ := value_rep r
    (Paper7Moments.integral_spec_entry (SG 6 p q) hG r hr) (by linarith)
    ((le_abs_self r).trans (Paper7C61Classification.spec_abs_le_six p q hn hG r hr))
  refine ⟨?_, ?_, i, ?_, ?_, ?_⟩
  · rw [actual_card p q hn hG]
    exact ((Paper7Admissible.lemma24_small_even_counts 6 p q (by decide) hG
      (by decide)).2 hn).1
  · have hs := (Paper7Admissible.lemma24_counting_even 6 p q (by decide) hG
      (by decide)).2.1
    have hm : (0 : ℝ) ≤ mult (SG 6 p q) 1 := Nat.cast_nonneg _
    have hnR : (nOf 6 p q : ℝ) ≤ 42 := by exact_mod_cast hn
    have hsq : (square (actual p q) : ℝ) ≤ 42 := by
      rw [actual_square p q hn hG]
      linarith
    exact_mod_cast hsq
  · rw [← hi] at hr3
    exact_mod_cast hr3
  · rw [actual_eq_mult, hi]
    exact hsimple
  · intro j hij
    rw [actual_eq_mult]
    apply Multiset.count_eq_zero_of_notMem
    intro hj
    have hjr : r < (value j : ℝ) := by
      rw [← hi]
      have hnat : value i < value j := by unfold value; omega
      exact_mod_cast hnat
    have hle := (le_abs_self (value j : ℝ)).trans (hmax (value j) hj).1
    linarith
#print axioms Paper7C61Profile.actual_admissible

end Paper7C61Profile
