import Research.Backfill.Paper7.RankCardinality
import Research.Backfill.Paper7.IntegralAbsPacking
import Research.Backfill.Paper7.SigmaSqBounds

/-! The two original support cases, including negative sigmaSq arguments. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Rank
open BackfillPaper7.Challenge

theorem rank_sigma_bound (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) :
    (sigmaSq ((bigEigs (SG b p q)).card : ℤ) : ℤ) ≤ 2 * (nOf b p q : ℤ) := by
  have h := rank_square_budget b p q hb hG
  omega
#print axioms Paper7Rank.rank_sigma_bound

theorem rank_sigma_nonempty (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) (hK : (Kq b q).Nonempty) :
    (sigmaSq ((b : ℤ) + (Kp b p).card - delta0 b p) : ℤ) ≤
      2 * (nOf b p q : ℤ) - 2 * (Kq b q).card := by
  have hr := rank_identity b p q hb hG
  have hp := Paper7Lemma22Gaps.deltaE_nonempty_bound b p q 1 hK
  have hn := Paper7Lemma22Gaps.deltaE_nonempty_bound b p q (-1) hK
  have h0 := rank0_nonneg b p hb
  have hle : (b : ℤ) + (Kp b p).card - delta0 b p ≤
      (bigEigs (SG b p q)).card := by omega
  have hs := sigmaSq_slope _ _ h0 hle
  have hB := rank_square_budget b p q hb hG
  have h1 := ((Paper7Lemma22.check_Lemma22 b p q hb).2.2.1 1 (Or.inl rfl)).1
  have h2 := ((Paper7Lemma22.check_Lemma22 b p q hb).2.2.1 (-1) (Or.inr rfl)).1
  have hQ := support_card_le_sum b q
  omega
#print axioms Paper7Rank.rank_sigma_nonempty

theorem rank_sigma_empty (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) (hK : Kq b q = ∅) :
    (sigmaSq ((b : ℤ) + (Kp b p).card - delta0 b p - 4) : ℤ) ≤
      2 * (nOf b p q : ℤ) - 4 := by
  have hn : b ≤ nOf b p q := by unfold nOf; omega
  by_cases hsmall : (b : ℤ) + (Kp b p).card - delta0 b p ≤ 4
  · rw [sigmaSq_eq_zero_of_nonpos _ (by omega)]
    omega
  · have hr := rank_identity b p q hb hG
    have hp := ((Paper7Lemma22.check_Lemma22 b p q hb).2.2.1 1 (Or.inl rfl)).2.2 hK
    have hm := ((Paper7Lemma22.check_Lemma22 b p q hb).2.2.1 (-1) (Or.inr rfl)).2.2 hK
    have hQ := support_sum_zero b q hK
    have h1 := ((Paper7Lemma22.check_Lemma22 b p q hb).2.2.1 1 (Or.inl rfl)).1
    have h2 := ((Paper7Lemma22.check_Lemma22 b p q hb).2.2.1 (-1) (Or.inr rfl)).1
    have hB := rank_square_budget b p q hb hG
    have hcard : (Kq b q).card = 0 := by rw [hK, Finset.card_empty]
    have h0 : 0 ≤ (b : ℤ) + (Kp b p).card - delta0 b p - 4 := by omega
    have hle : (b : ℤ) + (Kp b p).card - delta0 b p - 4 ≤
        (bigEigs (SG b p q)).card := by omega
    have hs := sigmaSq_slope _ _ h0 hle
    omega
#print axioms Paper7Rank.rank_sigma_empty

theorem cycle_length_le_thirteen (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hpos : 0 < ∑ k, (p k + q k)) (hG : IsIntegralGraph (SG b p q))
    (hn : nOf b p q ≤ 42) : b ≤ 13 := by
  have hr := rank_lower b p q hb hpos hG
  have hs := rank_sigma_bound b p q hb hG
  have hb14 : b ≤ 14 := by
    by_contra h
    have h11 : (11 : ℤ) ≤ (bigEigs (SG b p q)).card := by omega
    have ht := sigmaSq_monotone h11
    rw [sigmaSq_eleven] at ht
    have htZ : (100 : ℤ) ≤ sigmaSq ((bigEigs (SG b p q)).card : ℤ) := by
      exact_mod_cast ht
    omega
  by_contra h
  have he : b = 14 := by omega
  subst b
  have h0 := rank0_fourteen p
  by_cases hK : (Kq 14 q).Nonempty
  · have hbound := rank_sigma_nonempty 14 p q (by omega) hG hK
    norm_num only [Nat.cast_ofNat] at hbound
    have hmono := sigmaSq_monotone h0
    rw [sigmaSq_fourteen] at hmono
    have hmonoZ : (166 : ℤ) ≤ sigmaSq ((14 : ℤ) + (Kp 14 p).card - delta0 14 p) := by
      exact_mod_cast hmono
    omega
  · have hK0 : Kq 14 q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    have hbound := rank_sigma_empty 14 p q (by omega) hG hK0
    norm_num only [Nat.cast_ofNat] at hbound
    have h10 : (10 : ℤ) ≤ 14 + (Kp 14 p).card - delta0 14 p - 4 := by omega
    have hmono := sigmaSq_monotone h10
    rw [sigmaSq_ten] at hmono
    have hmonoZ : (84 : ℤ) ≤ sigmaSq ((14 : ℤ) + (Kp 14 p).card - delta0 14 p - 4) := by
      exact_mod_cast hmono
    omega
#print axioms Paper7Rank.cycle_length_le_thirteen

end Paper7Rank
