import Research.Backfill.Paper7.SpectralCardinalityCounts
import Research.Backfill.Paper7.Lemma22
import Research.Backfill.Paper7.SetupCardinality

/-! The rank identities and all support cases for frozen Lemma44. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Rank
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem support_card_le_sum (b : ℕ) (q : Fin b → ℕ) :
    (Kq b q).card ≤ ∑ k, q k := by
  have h := Paper7Reduced.freeQ_add_card b q
  change freeQ b q + (Kq b q).card = ∑ k, q k at h
  omega
#print axioms Paper7Rank.support_card_le_sum

theorem support_sum_zero (b : ℕ) (q : Fin b → ℕ) (hK : Kq b q = ∅) :
    (∑ k, q k) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k _
  have hk : ¬ 0 < q k := by
    intro h
    have : k ∈ Kq b q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [hK] at this
    exact Finset.notMem_empty k this
  omega
#print axioms Paper7Rank.support_sum_zero

theorem delta0_le_card_add_two (b : ℕ) (p : Fin b → ℕ) :
    delta0 b p ≤ (Kp b p).card + 2 := by
  classical
  by_cases hK : Kp b p = ∅
  · simp only [delta0, hK, ite_true, Finset.card_empty, zero_add]
    split <;> norm_num
  · rw [delta0, ite_eq_right hK]
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_right _ _)
#print axioms Paper7Rank.delta0_le_card_add_two

theorem delta0_le_card_of_nonempty (b : ℕ) (p : Fin b → ℕ)
    (hK : (Kp b p).Nonempty) : delta0 b p ≤ (Kp b p).card := by
  rw [delta0, ite_eq_right hK.ne_empty]
  exact Finset.card_filter_le _ _
#print axioms Paper7Rank.delta0_le_card_of_nonempty

theorem rank0_nonneg (b : ℕ) (p : Fin b → ℕ) (hb : 3 ≤ b) :
    0 ≤ (b : ℤ) + (Kp b p).card - delta0 b p := by
  have h := delta0_le_card_add_two b p
  omega
#print axioms Paper7Rank.rank0_nonneg

theorem rank_identity (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) :
    ((bigEigs (SG b p q)).card : ℤ) =
      (b : ℤ) + (Kp b p).card - delta0 b p + 2 * (Kq b q).card -
        deltaE b p q 1 - deltaE b p q (-1) := by
  have hc := Paper7Counting.integral_card_partition (spec (SG b p q))
    (Paper7Moments.small_integral_spec_entry _ hG)
  rw [Paper7Spectrum.spec_card] at hc
  change order b (pq b p q) = (bigEigs (SG b p q)).card +
    mult (SG b p q) 1 + mult (SG b p q) (-1) + mult (SG b p q) 0 at hc
  rw [Paper7Setup.sg_order] at hc
  have hz := (Paper7Lemma22.check_Lemma22 b p q hb).2.1
  have hp := ((Paper7Lemma22.check_Lemma22 b p q hb).2.2.1 1 (Or.inl rfl)).1
  have hn := ((Paper7Lemma22.check_Lemma22 b p q hb).2.2.1 (-1) (Or.inr rfl)).1
  unfold nOf at hc
  omega
#print axioms Paper7Rank.rank_identity

theorem rank_lower (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hpos : 0 < ∑ k, (p k + q k)) (hG : IsIntegralGraph (SG b p q)) :
    (b : ℤ) - 4 ≤ (bigEigs (SG b p q)).card := by
  have hr := rank_identity b p q hb hG
  by_cases hKq : (Kq b q).Nonempty
  · have hp := Paper7Lemma22Gaps.deltaE_nonempty_bound b p q 1 hKq
    have hn := Paper7Lemma22Gaps.deltaE_nonempty_bound b p q (-1) hKq
    have hz := delta0_le_card_add_two b p
    omega
  · have he : Kq b q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hKq
    have hp := ((Paper7Lemma22.check_Lemma22 b p q hb).2.2.1 1 (Or.inl rfl)).2.2 he
    have hn := ((Paper7Lemma22.check_Lemma22 b p q hb).2.2.1 (-1) (Or.inr rfl)).2.2 he
    have hKp : (Kp b p).Nonempty := by
      by_contra h
      have hep : Kp b p = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hsp := support_sum_zero b p hep
      have hsq := support_sum_zero b q he
      rw [Finset.sum_add_distrib, hsp, hsq] at hpos
      omega
    have hz := delta0_le_card_of_nonempty b p hKp
    simp only [he, Finset.card_empty, Nat.cast_zero] at hr
    omega
#print axioms Paper7Rank.rank_lower

theorem rank0_fourteen (p : Fin 14 → ℕ) :
    (14 : ℤ) ≤ 14 + (Kp 14 p).card - delta0 14 p := by
  classical
  by_cases hK : (Kp 14 p).Nonempty
  · have h := delta0_le_card_of_nonempty 14 p hK
    omega
  · have he : Kp 14 p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    norm_num [delta0, he]
#print axioms Paper7Rank.rank0_fourteen

end Paper7Rank
