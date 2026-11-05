import Research.Backfill.Paper7.C61PairTwoTotalTwentySix
import Research.Backfill.Paper7.C61FourOneTwoTwoThreesBetaFive
import Research.Backfill.Paper7.C61FourWithoutThreeQpositive

/-! NEW SOURCE ONLY. Complete original (m2,m3)=(2,1), q-positive,
beta-five branch, with every odd-coefficient sign covered. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Small Paper7C61Three
open scoped BigOperators Classical

theorem odd_zero_pair_two_total_twenty_six_impossible (p q : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hm : PairTwo p q) (hL : totalP 6 p+totalQ 6 q=26)
    (hQ : totalQ 6 q ≤ 10) : False := by
  have hLN : p 0+p 2+p 4+q 0+q 1+q 2+q 3+q 4+q 5=26 := by
    norm_num [totalP, totalQ, Fin.sum_univ_six, hp1, hp3, hp5] at hL
    omega
  have hLR : (p 0 : ℝ)+p 2+p 4+q 0+q 1+q 2+q 3+q 4+q 5=26 := by
    exact_mod_cast hLN
  have hBudget : (q 0+q 2+q 4)+q 1+q 3+q 5 ≤ 10 := by
    norm_num [totalQ, Fin.sum_univ_six] at hQ
    omega
  apply pair_two_total_twenty_six_impossible
    (coefficientTwo p q 0) (coefficientTwo p q 2) (coefficientTwo p q 4)
    (q 1) (q 3) (q 5) (q 0+q 2+q 4) hBudget
  · norm_num [coefficientTwo, Nat.cast_add]
    nlinarith only [hLR]
  · have hh := hm.1
    norm_num [coefficientTwo, oddTwoCoefficient, hp1, hp3, hp5] at hh ⊢
    nlinarith only [hh]
  · have hh := hm.2.1
    norm_num [coefficientTwo, oddTwoCoefficient, hp1, hp3, hp5] at hh ⊢
    nlinarith only [hh]
  · have hh := hm.2.2
    norm_num [coefficientTwo, oddTwoCoefficient, hp1, hp3, hp5] at hh ⊢
    nlinarith only [hh]
#print axioms Paper7C61Four.odd_zero_pair_two_total_twenty_six_impossible

theorem alpha_six_pair_two_total_twenty_six_impossible (p q : Fin 6 → ℕ)
    (ha : zeroExponent p=6) (hm : PairTwo p q)
    (hL : totalP 6 p+totalQ 6 q=26) (hQ : totalQ 6 q ≤ 10) : False := by
  rcases alpha_six_parity p ha with hp | hp
  · exact odd_zero_pair_two_total_twenty_six_impossible p q hp.1 hp.2.1 hp.2.2 hm hL hQ
  · exact odd_zero_pair_two_total_twenty_six_impossible (shiftSix p) (shiftSix q)
      (by simpa [shiftSix] using hp.2.1)
      (by simpa [shiftSix] using hp.2.2)
      (by simpa [shiftSix] using hp.1) (pair_two_shift p q hm)
      (by rwa [total_shift]) (by rwa [q_total_shift])
#print axioms Paper7C61Four.alpha_six_pair_two_total_twenty_six_impossible

theorem root_four_two_twos_one_three_qpositive_beta_five_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h0 : (actual p q 0).val=2)
    (h1 : (actual p q 1).val=1) (hK : (Kq 6 q).Nonempty)
    (hb : unitExponent p q=5) : False := by
  have _hK := hK
  obtain ⟨hc, hs, _hf⟩ := root_four_profile (actual p q) h4
  rw [h0, h1] at hc hs
  have he := exponent_budget p q hn hG
  have ha : zeroExponent p=6 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hL : totalP 6 p+totalQ 6 q=26 := by omega
  have hn' : 6+totalP 6 p+2*totalQ 6 q ≤ 42 := hn
  have hQ : totalQ 6 q ≤ 10 := by omega
  exact alpha_six_pair_two_total_twenty_six_impossible p q ha
    (actual_two_twice_pair_two p q h0) hL hQ
#print axioms Paper7C61Four.root_four_two_twos_one_three_qpositive_beta_five_impossible

end Paper7C61Four
