import Research.Backfill.Paper7.Lemma41
import Research.Backfill.Paper7.TwelveCycleUnitRank
import Research.Backfill.Paper7.ZeroGapParity

/-! NEW SOURCE ONLY. Necessary rank equalities for the actual eight-cycle.
The mixed case conclusions are derived from the original graph assumptions. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem eight_big_card_bounds (p q : Fin 8 → ℕ)
    (hp : 0 < ∑ i, (p i+q i)) (hn : nOf 8 p q ≤ 41)
    (hG : IsIntegralGraph (SG 8 p q)) :
    3 ≤ (Bplus (SG 8 p q)).card ∧ (Bplus (SG 8 p q)).card ≤ 4 := by
  have hlo := (Paper7Lemma41.check_Lemma41 8 p q (by decide)).2.2.2 hG hp
  have hhi := Paper7Admissible.lemma24_small_even_counts 8 p q (by decide) hG (by decide)
  have hlower := hlo.1
  norm_num at hlower
  exact ⟨hlower,hhi.1 hn⟩
#print axioms Paper7EightCycle.eight_big_card_bounds

theorem eight_mixed_rank_saturated (p q : Fin 8 → ℕ)
    (hp : 0 < ∑ i, p i) (hq : 0 < ∑ i, q i) (hn : nOf 8 p q ≤ 41)
    (hG : IsIntegralGraph (SG 8 p q)) :
    (Bplus (SG 8 p q)).card = 4 ∧ delta0 8 p = (Kp 8 p).card ∧
      deltaE 8 p q 1 = (Kq 8 q).card ∧ deltaE 8 p q (-1) = (Kq 8 q).card ∧
      mult (SG 8 p q) 1 = ∑ i, q i ∧
      S2 (SG 8 p q) = 8+(∑ i, p i : ℕ)+(∑ i, q i : ℕ) := by
  have hpq : 0 < ∑ i, (p i+q i) := by rw [Finset.sum_add_distrib]; omega
  have hKP : (Kp 8 p).Nonempty := by
    by_contra hh
    have hz := Paper7Rank.support_sum_zero 8 p (Finset.not_nonempty_iff_eq_empty.mp hh)
    omega
  have hKQ : (Kq 8 q).Nonempty := by
    by_contra hh
    have hz := Paper7Rank.support_sum_zero 8 q (Finset.not_nonempty_iff_eq_empty.mp hh)
    omega
  have hd := Paper7Rank.delta0_le_card_of_nonempty 8 p hKP
  have hdp := Paper7Lemma22Gaps.deltaE_nonempty_bound 8 p q 1 hKQ
  have hdm := Paper7Lemma22Gaps.deltaE_nonempty_bound 8 p q (-1) hKQ
  have hr := Paper7Rank.rank_identity 8 p q (by decide) hG
  have he := Paper7Admissible.lemma24_counting_even 8 p q (by decide) hG (by decide)
  have hcard := Paper7Counting.symmetric_big_card (SG 8 p q) he.1
  have hupper := (eight_big_card_bounds p q hpq hn hG).2
  have hc : (Bplus (SG 8 p q)).card = 4 := by omega
  have hz : delta0 8 p = (Kp 8 p).card := by omega
  have hplus : deltaE 8 p q 1 = (Kq 8 q).card := by omega
  have hminus : deltaE 8 p q (-1) = (Kq 8 q).card := by omega
  have hoff := ((Paper7Lemma22.check_Lemma22 8 p q (by decide)).2.2.1 1 (Or.inl rfl)).1
  have hm : mult (SG 8 p q) 1 = ∑ i, q i := by omega
  refine ⟨hc,hz,hplus,hminus,hm,?_⟩
  have hsum := he.2.1
  rw [hm] at hsum
  unfold nOf at hsum
  push_cast at hsum ⊢
  linarith only [hsum]
#print axioms Paper7EightCycle.eight_mixed_rank_saturated

theorem eight_saturated_rotated_odd_zero (p : Fin 8 → ℕ)
    (hd : delta0 8 p = (Kp 8 p).card) (k : Fin 8) (hk : 0 < p k) :
    ∀ i : Fin 8, Odd i.val → p (i+k) = 0 := by
  intro i hi
  have hrot : ((finRotate 8)^i.val) k = i+k := by
    fin_cases i <;> fin_cases k <;> decide
  rw [← hrot]
  exact Paper7MainReduction.saturated_zero_gap_odd_rotation 8 p hd i.val k hk hi i.isLt
#print axioms Paper7EightCycle.eight_saturated_rotated_odd_zero

end Paper7EightCycle
