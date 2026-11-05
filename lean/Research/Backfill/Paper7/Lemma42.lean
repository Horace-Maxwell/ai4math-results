import Research.Backfill.Paper7.SpectralCardinalityCounts
import Research.Backfill.Paper7.Lemma24Counting
import Research.Backfill.Paper7.SetupCardinality

/-! Complete frozen Lemma42 candidate. No positive-pendant hypothesis is used. -/
set_option autoImplicit false
noncomputable section

namespace Paper7Counting
open BackfillPaper7.Challenge

/-- All three exact multiplicities, including bare even cycles. -/
theorem lemma42_multiplicities (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (he : Even b) (hG : IsIntegralGraph (SG b p q)) :
    (mult (SG b p q) 1 : ℝ) = nOf b p q - S2 (SG b p q) ∧
    (mult (SG b p q) (-1) : ℝ) = nOf b p q - S2 (SG b p q) ∧
    (mult (SG b p q) 0 : ℝ) = 2 * S2 (SG b p q) - nOf b p q -
      2 * Multiset.card (Bplus (SG b p q)) := by
  have h := Paper7Admissible.lemma24_counting_even b p q hb hG he
  have hS := h.2.1
  have hp : (mult (SG b p q) 1 : ℝ) = nOf b p q - S2 (SG b p q) := by
    linarith
  have hn : (mult (SG b p q) (-1) : ℝ) = nOf b p q - S2 (SG b p q) := by
    rw [← h.1 1]
    exact hp
  have hcN := symmetric_spectrum_card (SG b p q) hG h.1
  change order b (pq b p q) = _ at hcN
  rw [Paper7Setup.sg_order b p q] at hcN
  have hc : (nOf b p q : ℝ) = 2 * ((Bplus (SG b p q)).card : ℝ) +
      (mult (SG b p q) 1 : ℝ) + (mult (SG b p q) (-1) : ℝ) +
      (mult (SG b p q) 0 : ℝ) := by
    exact_mod_cast hcN
  refine ⟨hp, hn, ?_⟩
  linarith
#print axioms Paper7Counting.lemma42_multiplicities

/-- The three inequalities follow from nonnegative multiplicities and Lemma22. -/
theorem lemma42_bounds (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (he : Even b) (hG : IsIntegralGraph (SG b p q)) :
    S2 (SG b p q) ≤ nOf b p q ∧
    (nOf b p q : ℝ) ≤ 2 * S2 (SG b p q) -
      2 * Multiset.card (Bplus (SG b p q)) ∧
    2 * S2 (SG b p q) - nOf b p q - 2 * Multiset.card (Bplus (SG b p q)) ≤
      (max (∑ k, p k) 2 : ℕ) := by
  rcases lemma42_multiplicities b p q hb he hG with ⟨hp, _, h0⟩
  have hp_nonneg : (0 : ℝ) ≤ mult (SG b p q) 1 := Nat.cast_nonneg _
  have h0_nonneg : (0 : ℝ) ≤ mult (SG b p q) 0 := Nat.cast_nonneg _
  have hboundN := (Paper7Lemma22.check_Lemma22 b p q hb).2.2.2.1
  have hbound : (mult (SG b p q) 0 : ℝ) ≤ (max (∑ k, p k) 2 : ℕ) := by
    exact_mod_cast hboundN
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
#print axioms Paper7Counting.lemma42_bounds

theorem check_Lemma42 : BackfillPaper7.Challenge.Lemma42 := by
  intro b p q hb he hG
  rcases lemma42_multiplicities b p q hb he hG with ⟨hp, hn, h0⟩
  rcases lemma42_bounds b p q hb he hG with ⟨hS, hnS, hZ⟩
  exact ⟨hp, hn, h0, hS, hnS, hZ⟩
#print axioms Paper7Counting.check_Lemma42

end Paper7Counting
