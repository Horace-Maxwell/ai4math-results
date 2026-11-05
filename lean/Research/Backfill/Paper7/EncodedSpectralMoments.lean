import Research.Backfill.Paper7.ActualSpectralCounts
import Research.Backfill.Paper7.BoundedSpectralSums
import Research.Backfill.Paper7.SunTheta

/-! Source-only bridges from the actual encoded multiplicities to the real
moments, preserving the even positive-half and odd full-spectrum conventions. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningSpectrum
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem encoded_s2_even (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) (he : Even b) :
    (s2 b (actualCounts b x hb) : ℝ) = S2 (SG b x.1 x.2) := by
  have h := positive_sum (SG b x.1 x.2) hG (budget_spectral_window b N x hb hN hx)
    (fun a : ℝ => a ^ 2)
  simpa [s2, S2, actualCounts, he] using h.symm
#print axioms Paper7PruningSpectrum.encoded_s2_even

theorem encoded_s2_odd (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) (ho : Odd b) :
    (s2 b (actualCounts b x hb) : ℝ) =
      ((bigEigs (SG b x.1 x.2)).map (fun a : ℝ => a ^ 2)).sum := by
  rw [big_sum (SG b x.1 x.2) hG (budget_spectral_window b N x hb hN hx)]
  simp only [s2, ite_eq_right (Nat.not_even_iff_odd.mpr ho)]
  push_cast
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [actualCounts_pos, actualCounts_neg_odd b x hb ho]
  ring
#print axioms Paper7PruningSpectrum.encoded_s2_odd

theorem encoded_quartic (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    ((bigEigs (SG b x.1 x.2)).map (fun a : ℝ => a ^ 2 * (a ^ 2 - 1))).sum =
      if Even b then 2 * (m4 b (actualCounts b x hb) : ℝ)
      else (m4 b (actualCounts b x hb) : ℝ) := by
  rw [big_sum (SG b x.1 x.2) hG (budget_spectral_window b N x hb hN hx)]
  rw [← sum_add_distrib]
  by_cases he : Even b
  · simp only [ite_eq_left he, m4, add_zero]
    push_cast
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    have hsym := (Paper7Admissible.lemma24_counting_even b x.1 x.2 hb hG he).1
    rw [← hsym (value i), actualCounts_pos]
    ring
  · have ho := Nat.not_even_iff_odd.mp he
    simp only [ite_eq_right he, m4]
    push_cast
    apply sum_congr rfl
    intro i _
    rw [actualCounts_pos, actualCounts_neg_odd b x hb ho]
    ring
#print axioms Paper7PruningSpectrum.encoded_quartic

theorem encoded_odd_moment (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) (ho : Odd b)
    (L : ℕ) (hL : Odd L) :
    (((∑ i : Fin 8, (((actualCounts b x hb).1 i).val -
        ((actualCounts b x hb).2 i).val : ℤ) * ((value i : ℤ)^L - value i)) : ℤ) : ℝ) =
      ((bigEigs (SG b x.1 x.2)).map (fun a : ℝ => a^L-a)).sum := by
  rw [big_sum (SG b x.1 x.2) hG (budget_spectral_window b N x hb hN hx)]
  push_cast
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [actualCounts_pos, actualCounts_neg_odd b x hb ho, hL.neg_pow]
  ring
#print axioms Paper7PruningSpectrum.encoded_odd_moment

theorem actualCounts_m4 (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    m4 b (actualCounts b x hb) =
      if Even b then theta x + (if b = 4 then 4 else 0) else 2 * theta x := by
  have h := Paper7SunMoments.sg_big_quartic_moment b x.1 x.2 hb hG
  rw [encoded_quartic b N x hb hN hx hG, Paper7Setup.sg_theta b x.1 x.2 hb] at h
  change (if Even b then 2 * (m4 b (actualCounts b x hb) : ℝ)
    else (m4 b (actualCounts b x hb) : ℝ)) =
      2 * (theta x : ℝ) + 8 * (if b = 4 then (1 : ℝ) else 0) at h
  by_cases he : Even b <;> by_cases h4 : b = 4
  · simp only [ite_eq_left he, ite_eq_left h4] at h ⊢
    have hr : (m4 b (actualCounts b x hb) : ℝ) = (theta x : ℝ) + 4 := by linarith
    exact_mod_cast hr
  · simp only [ite_eq_left he, ite_eq_right h4, add_zero] at h ⊢
    have hr : (m4 b (actualCounts b x hb) : ℝ) = (theta x : ℝ) := by linarith
    exact_mod_cast hr
  · subst b
    norm_num at he
  · simp only [ite_eq_right he, ite_eq_right h4] at h ⊢
    have hr : (m4 b (actualCounts b x hb) : ℝ) = 2 * (theta x : ℝ) := by linarith
    exact_mod_cast hr
#print axioms Paper7PruningSpectrum.actualCounts_m4

theorem actualCounts_targetTheta (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    targetTheta b (actualCounts b x hb) = theta x := by
  rw [targetTheta, actualCounts_m4 b N x hb hN hx hG]
  by_cases he : Even b <;> simp [he]
#print axioms Paper7PruningSpectrum.actualCounts_targetTheta

end Paper7PruningSpectrum
