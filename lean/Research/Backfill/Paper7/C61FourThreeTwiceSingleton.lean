import Research.Backfill.Paper7.C61SingletonDivisibilityRotation
import Research.Backfill.Paper7.C61RootFourReduction

/-! NEW SOURCE ONLY. Complete original repeated-three, beta-six,
q-singleton branch. The singleton can be at any of the six sites. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Small
open scoped Classical

theorem q_support_card_one_unique (q : Fin 6 → ℕ) (hK : (Kq 6 q).card=1) :
    ∃ k : Fin 6, ∀ j : Fin 6, j ≠ k → q j=0 := by
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hK
  refine ⟨k, ?_⟩
  intro j hj
  by_contra hn
  have hjK : j ∈ Kq 6 q := Finset.mem_filter.mpr
    ⟨Finset.mem_univ j, Nat.pos_of_ne_zero hn⟩
  rw [hk] at hjK
  exact hj (Finset.mem_singleton.mp hjK)
#print axioms Paper7C61Four.q_support_card_one_unique

theorem root_four_one_two_two_threes_qpositive_beta_six_singleton_impossible
    (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h0 : (actual p q 0).val=1)
    (h1 : (actual p q 1).val=2) (hb : unitExponent p q=6)
    (hK : (Kq 6 q).card=1) : False := by
  obtain ⟨_hc, hs, _hf⟩ := root_four_profile (actual p q) h4
  rw [h0, h1] at hs
  have hsum := parameter_sum_eq_profile p q hn hG
  have hL : totalP 6 p+totalQ 6 q=32 := by omega
  have hn' : 6+totalP 6 p+2*totalQ 6 q ≤ 42 := hn
  have hQ4 : totalQ 6 q ≤ 4 := by omega
  have hcard := Paper7Rank.support_card_le_sum 6 q
  change (Kq 6 q).card ≤ totalQ 6 q at hcard
  have hQpos : 0 < totalQ 6 q := by omega
  have hd := mono_three_singleton_total_divisible_eight p q
    (actual_three_monodromy p q h1) (q_support_card_one_unique q hK)
  obtain ⟨t, ht⟩ := hd
  omega
#print axioms Paper7C61Four.root_four_one_two_two_threes_qpositive_beta_six_singleton_impossible

end Paper7C61Four
