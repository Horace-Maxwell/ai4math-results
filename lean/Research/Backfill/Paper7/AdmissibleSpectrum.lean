import Research.Backfill.Paper7.EncodedSpectralMoments

/-! Source-only proof of the original actual-spectrum admissible encoding.
Every finite entry is a genuine real-spectrum multiplicity; no feature oracle. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningSpectrum
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem actualCounts_perron (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    ∃ ρ : Fin 8, 3 ≤ value ρ ∧ (actualCounts b x hb).1 ρ = 1 ∧
      (∀ i, value ρ < value i → (actualCounts b x hb).1 i = 0) ∧
      (if Even b then (actualCounts b x hb).2 = 0
       else ∀ i, value ρ ≤ value i → (actualCounts b x hb).2 i = 0) := by
  obtain ⟨r, hr, hsimple, hr3, hmax⟩ := Paper7Admissible.lemma24_perron b x.1 x.2 hb
    (budget_pendants_positive b N x hx) hG
  have hwin := budget_spectral_window b N x hb hN hx
  obtain ⟨ρ, hρ⟩ := positive_value_rep r
    (Paper7Moments.integral_spec_entry (SG b x.1 x.2) hG r hr)
    (by linarith) ((le_abs_self r).trans_lt (hwin r hr))
  have hρ3 : 3 ≤ value ρ := by rw [← hρ] at hr3; exact_mod_cast hr3
  refine ⟨ρ, hρ3, ?_, ?_, ?_⟩
  · apply Fin.ext
    change mult (SG b x.1 x.2) (value ρ) = 1
    rw [hρ]
    exact hsimple
  · intro i hi
    have hir : r < (value i : ℝ) := by
      rw [← hρ]
      exact_mod_cast hi
    have hn : (value i : ℝ) ∉ spec (SG b x.1 x.2) := by
      intro hm
      have hle := (le_abs_self (value i : ℝ)).trans (hmax (value i) hm).1
      linarith
    apply Fin.ext
    exact Multiset.count_eq_zero_of_notMem hn
  · by_cases he : Even b
    · simpa only [ite_eq_left he] using actualCounts_neg_even b x hb he
    · simp only [ite_eq_right he]
      intro i hi
      have ho := Nat.not_even_iff_odd.mp he
      have hri : r ≤ (value i : ℝ) := by rw [← hρ]; exact_mod_cast hi
      have hn : -(value i : ℝ) ∉ spec (SG b x.1 x.2) := by
        intro hm
        have hlt := (hmax (-(value i : ℝ)) hm).2.2 ho
        linarith
      apply Fin.ext
      rw [actualCounts_neg_odd b x hb ho]
      exact Multiset.count_eq_zero_of_notMem hn
#print axioms Paper7PruningSpectrum.actualCounts_perron

theorem actualCounts_s2_budget (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    s2 b (actualCounts b x hb) ≤ if Even b then (N : ℤ) else 2 * N := by
  have hn : nOf b x.1 x.2 ≤ N := by rw [nOf_eq_b_weight]; exact hx.2
  have hnR : (nOf b x.1 x.2 : ℝ) ≤ N := by exact_mod_cast hn
  by_cases he : Even b
  · rw [ite_eq_left he]
    have hcount := (Paper7Admissible.lemma24_counting_even b x.1 x.2 hb hG he).2.1
    have hmult : (0 : ℝ) ≤ mult (SG b x.1 x.2) 1 := by positivity
    have hr : (s2 b (actualCounts b x hb) : ℝ) ≤ N := by
      rw [encoded_s2_even b N x hb hN hx hG he]
      linarith
    exact_mod_cast hr
  · rw [ite_eq_right he]
    have ho := Nat.not_even_iff_odd.mp he
    have hp := Paper7Admissible.graph_square_partition (SG b x.1 x.2) hG
    rw [Paper7SunMoments.sg_second_moment b x.1 x.2 hb] at hp
    have hpos : (0 : ℝ) ≤ mult (SG b x.1 x.2) 1 := by positivity
    have hneg : (0 : ℝ) ≤ mult (SG b x.1 x.2) (-1) := by positivity
    have hr : (s2 b (actualCounts b x hb) : ℝ) ≤ 2 * N := by
      rw [encoded_s2_odd b N x hb hN hx hG ho]
      linarith
    exact_mod_cast hr
#print axioms Paper7PruningSpectrum.actualCounts_s2_budget

theorem actualCounts_odd_moments (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) (ho : Odd b)
    (L : ℕ) (hL : Odd L) (_hL3 : 3 ≤ L) (hLb : L ≤ b) :
    (∑ i, (((actualCounts b x hb).1 i).val - ((actualCounts b x hb).2 i).val : ℤ) *
      ((value i : ℤ)^L - value i)) = if L = b then 2 * b else 0 := by
  have h := encoded_odd_moment b N x hb hN hx hG ho L hL
  by_cases hEq : L = b
  · subst L
    rw [Paper7SunMoments.sg_big_odd_moment_at_cycle b x.1 x.2 hb hG ho] at h
    simp only [ite_true]
    exact_mod_cast h
  · rw [ite_eq_right hEq]
    rw [Paper7SunMoments.sg_big_odd_moment_below b x.1 x.2 hb hG L hL
      (by omega)] at h
    exact_mod_cast h
#print axioms Paper7PruningSpectrum.actualCounts_odd_moments

theorem actualCounts_admissibleBase (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    AdmissibleBase b N (actualCounts b x hb) := by
  exact ⟨actualCounts_perron b N x hb hN hx hG,
    actualCounts_s2_budget b N x hb hN hx hG,
    actualCounts_odd_moments b N x hb hN hx hG⟩
#print axioms Paper7PruningSpectrum.actualCounts_admissibleBase

/-- Exactly original pruning conjunct 3, without an added non-cycle premise. -/
theorem pruning_actual_spectrum_encoding :
    ∀ b N : ℕ, 3 ≤ b → b ≤ N → N ≤ 49 → ∀ x, Budget b N x →
      IsIntegralGraph (SG b x.1 x.2) →
      ∃ s, AdmissibleBase b N s ∧
        (∀ i : Fin 8, (s.1 i).val = mult (SG b x.1 x.2) (value i)) ∧
        (Odd b → ∀ i : Fin 8, (s.2 i).val = mult (SG b x.1 x.2) (-(value i : ℝ))) := by
  intro b N hb _hbN hN x hx hG
  exact ⟨actualCounts b x hb, actualCounts_admissibleBase b N x hb hN hx hG,
    actualCounts_pos b x hb, actualCounts_neg_odd b x hb⟩
#print axioms Paper7PruningSpectrum.pruning_actual_spectrum_encoding

end Paper7PruningSpectrum
