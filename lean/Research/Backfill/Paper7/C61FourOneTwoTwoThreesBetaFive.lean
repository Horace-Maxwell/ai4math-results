import Research.Backfill.Paper7.C61AlternatingPairAlgebra
import Research.Backfill.Paper7.C61RootFourReduction
import Research.Backfill.Paper7.C61AlphaSixParity

/-! NEW SOURCE ONLY. Complete original (m2,m3)=(1,2), q-positive,
beta-five branch, using the actual repeated eigenvalue-three monodromy. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Small Paper7C61Three
open scoped BigOperators Classical

theorem alternating_pair_positive_even (a c e x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hax : 0 < x+z-y) (hcx : 0 < x+y-z) (hex : 0 < y+z-x)
    (h0 : a*x+e*y=2) (h1 : c*x+e*z=2) (h2 : c*y+a*z=2) :
    0 < a ∧ 0 < c ∧ 0 < e := by
  obtain ⟨ha, hc, he⟩ := alternating_pair_coordinate_products a c e x y z h0 h1 h2
  have hxz := mul_pos hx hz
  have hxy := mul_pos hx hy
  have hyz := mul_pos hy hz
  constructor
  · by_contra hn
    have hn' : a ≤ 0 := by linarith
    have hm := mul_nonpos_of_nonpos_of_nonneg hn' hxz.le
    nlinarith only [ha, hax, hm]
  constructor
  · by_contra hn
    have hn' : c ≤ 0 := by linarith
    have hm := mul_nonpos_of_nonpos_of_nonneg hn' hxy.le
    nlinarith only [hc, hcx, hm]
  · by_contra hn
    have hn' : e ≤ 0 := by linarith
    have hm := mul_nonpos_of_nonpos_of_nonneg hn' hyz.le
    nlinarith only [he, hex, hm]
#print axioms Paper7C61Four.alternating_pair_positive_even

theorem coefficient_three_positive_p_le_eight (p q : Fin 6 → ℕ) (k : Fin 6)
    (h : 0 < coefficientThree p q k) : p k ≤ 8 := by
  unfold coefficientThree at h
  have hqR : (0 : ℝ) ≤ q k := Nat.cast_nonneg (q k)
  have hpR : (p k : ℝ) < 9 := by nlinarith
  have hpN : p k < 9 := by exact_mod_cast hpR
  omega
#print axioms Paper7C61Four.coefficient_three_positive_p_le_eight

theorem odd_zero_pair_three_qfive_p_bound (p q : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hm : PairThree p q) (hQ : totalQ 6 q ≤ 5) : totalP 6 p ≤ 24 := by
  have hQo : q 1+q 3+q 5 ≤ 5 := by
    norm_num [totalQ, Fin.sum_univ_six] at hQ
    omega
  have hQR : (q 1 : ℝ)+q 3+q 5 ≤ 5 := by exact_mod_cast hQo
  have hq1 : (0 : ℝ) ≤ q 1 := Nat.cast_nonneg (q 1)
  have hq3 : (0 : ℝ) ≤ q 3 := Nat.cast_nonneg (q 3)
  have hq5 : (0 : ℝ) ≤ q 5 := Nat.cast_nonneg (q 5)
  have hb : 0 < coefficientThree p q 1 ∧ 0 < coefficientThree p q 3 ∧
      0 < coefficientThree p q 5 ∧
      0 < coefficientThree p q 1+coefficientThree p q 5-coefficientThree p q 3 ∧
      0 < coefficientThree p q 1+coefficientThree p q 3-coefficientThree p q 5 ∧
      0 < coefficientThree p q 3+coefficientThree p q 5-coefficientThree p q 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [coefficientThree, hp1, hp3, hp5] <;> nlinarith
  have he := alternating_pair_positive_even
    (coefficientThree p q 0) (coefficientThree p q 2) (coefficientThree p q 4)
    (coefficientThree p q 1) (coefficientThree p q 3) (coefficientThree p q 5)
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
    (by nlinarith only [hm.1]) (by nlinarith only [hm.2.1]) (by nlinarith only [hm.2.2])
  have hp0 := coefficient_three_positive_p_le_eight p q 0 he.1
  have hp2 := coefficient_three_positive_p_le_eight p q 2 he.2.1
  have hp4 := coefficient_three_positive_p_le_eight p q 4 he.2.2
  norm_num [totalP, Fin.sum_univ_six, hp1, hp3, hp5]
  omega
#print axioms Paper7C61Four.odd_zero_pair_three_qfive_p_bound

theorem q_total_shift (q : Fin 6 → ℕ) : totalQ 6 (shiftSix q) = totalQ 6 q := by
  norm_num [totalQ, shiftSix, Fin.sum_univ_six]
  omega
#print axioms Paper7C61Four.q_total_shift

theorem alpha_six_pair_three_total_thirty_one_impossible (p q : Fin 6 → ℕ)
    (ha : zeroExponent p = 6) (hm : PairThree p q)
    (hL : totalP 6 p+totalQ 6 q=31) (hQ : totalQ 6 q ≤ 5) : False := by
  rcases alpha_six_parity p ha with hp | hp
  · have hb := odd_zero_pair_three_qfive_p_bound p q hp.1 hp.2.1 hp.2.2 hm hQ
    omega
  · have hb := odd_zero_pair_three_qfive_p_bound (shiftSix p) (shiftSix q)
      (by simpa [shiftSix] using hp.2.1)
      (by simpa [shiftSix] using hp.2.2)
      (by simpa [shiftSix] using hp.1) (pair_three_shift p q hm)
      (by rwa [q_total_shift])
    have hLs : totalP 6 (shiftSix p)+totalQ 6 (shiftSix q)=31 := by
      rwa [total_shift]
    rw [q_total_shift] at hLs
    omega
#print axioms Paper7C61Four.alpha_six_pair_three_total_thirty_one_impossible

theorem root_four_one_two_two_threes_qpositive_beta_five_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h0 : (actual p q 0).val = 1)
    (h1 : (actual p q 1).val = 2) (hK : (Kq 6 q).Nonempty)
    (hb : unitExponent p q = 5) : False := by
  have _hK := hK
  obtain ⟨hc, hs, _hf⟩ := root_four_profile (actual p q) h4
  rw [h0, h1] at hc hs
  have he := exponent_budget p q hn hG
  have ha : zeroExponent p = 6 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hL : totalP 6 p+totalQ 6 q=31 := by omega
  have hn' : 6+totalP 6 p+2*totalQ 6 q ≤ 42 := hn
  have hQ : totalQ 6 q ≤ 5 := by omega
  exact alpha_six_pair_three_total_thirty_one_impossible p q ha
    (actual_three_twice_pair_three p q h1) hL hQ
#print axioms Paper7C61Four.root_four_one_two_two_threes_qpositive_beta_five_impossible

end Paper7C61Four
