import Research.Backfill.Paper7.C61ThreeEvenMoments
import Research.Backfill.Paper7.C61PerronFiveThreeMoments

/-! NEW SOURCE ONLY. A complete capped-moment obstruction for the original
one-two/one-three, beta-seven, zero-q Perron-four branch. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Higher
open Paper7C61Three Paper7C61FiveThree
open scoped BigOperators Classical

theorem no_sum_six_square_twenty_four (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 6) (hS : squares 6 p = 24) : False := by
  obtain ⟨M,hM0,_hMP,hmax,hlow,hupp⟩ := maximum_moment_interval p 6 24 hP hS
  norm_num at hmax hlow hupp
  have hM4 : 4 ≤ M := by omega
  have hMlt : M < 5 := by
    by_contra hn
    have hM5 : 5 ≤ M := by omega
    have hmul := mul_nonneg (sub_nonneg.mpr hM5) hM0
    nlinarith
  have heq : M = 4 := by omega
  rw [heq] at hupp
  norm_num at hupp
#print axioms Paper7C61Four.no_sum_six_square_twenty_four

theorem cap_six_sum_twelve_square_sixty_impossible (r : Fin 6 → ℕ)
    (hcap : ∀ i, r i ≤ 6) (hP : totalP 6 r = 12) (hS : squares 6 r = 60) : False := by
  by_cases hsmall : ∀ i, r i ≤ 5
  · have hle (i : Fin 6) : r i^2 ≤ 5*r i := by nlinarith [hsmall i]
    have heq : ∀ i, r i^2 = 5*r i := equal_sums_pointwise _ _ hle (by
      change squares 6 r = ∑ i, 5*r i
      rw [← Finset.mul_sum]
      change squares 6 r = 5*totalP 6 r
      rw [hP,hS])
    have hdiv (i : Fin 6) : 5 ∣ r i := by
      have hi : (r i : ℤ)^2 = 5*(r i : ℤ) := by exact_mod_cast heq i
      have hz : (r i : ℤ)*((r i : ℤ)-5) = 0 := by nlinarith only [hi]
      rcases mul_eq_zero.mp hz with h0 | h5
      · have hr0 : r i = 0 := by exact_mod_cast h0
        rw [hr0]
        exact dvd_zero 5
      · have hr5 : r i = 5 := by omega
        simpa only [hr5] using (dvd_refl (5 : ℕ))
    have hd : 5 ∣ totalP 6 r := by
      unfold totalP
      exact Finset.dvd_sum (fun i _hi => hdiv i)
    rw [hP] at hd
    norm_num at hd
  · push Not at hsmall
    obtain ⟨k,hk⟩ := hsmall
    have hk6 : r k = 6 := by have hc := hcap k; omega
    obtain ⟨s,hsP,hsS⟩ := erase_coordinate_moments r k
    rw [hk6,hP] at hsP
    rw [hk6,hS] at hsS
    exact no_sum_six_square_twenty_four s (by omega) (by norm_num at hsS; omega)
#print axioms Paper7C61Four.cap_six_sum_twelve_square_sixty_impossible

theorem support_four_cap_thirteen_sum_twenty_four_square_240_impossible
    (p : Fin 6 → ℕ) (hK : (Kp 6 p).card ≤ 4) (hcap : ∀ i, p i ≤ 13)
    (hP : totalP 6 p = 24) (hS : squares 6 p = 240) : False := by
  have hEven := support_four_square_multiple_eight_even p hK (by rw [hS]; norm_num)
  have hex (i : Fin 6) : ∃ n : ℕ, p i = 2*n := hEven i
  choose r hr using hex
  have hrcap (i : Fin 6) : r i ≤ 6 := by
    have hi := hcap i
    rw [hr i] at hi
    omega
  have hPscale : totalP 6 p = 2*totalP 6 r := by
    unfold totalP
    simp_rw [hr]
    exact (Finset.mul_sum _ _ _).symm
  have hSscale : squares 6 p = 4*squares 6 r := by
    unfold squares
    simp_rw [hr,mul_pow]
    norm_num
    exact (Finset.mul_sum _ _ _).symm
  exact cap_six_sum_twelve_square_sixty_impossible r hrcap (by omega) (by omega)
#print axioms Paper7C61Four.support_four_cap_thirteen_sum_twenty_four_square_240_impossible

theorem alpha_four_support_le_four (p : Fin 6 → ℕ) (ha : zeroExponent p = 4) :
    (Kp 6 p).card ≤ 4 := by
  have hd := support_add_delta0_le_six p
  have hc : (Kp 6 p).card ≤ 6 := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Kp 6 p))
  unfold zeroExponent at ha
  omega
#print axioms Paper7C61Four.alpha_four_support_le_four

theorem root_four_one_two_one_three_qzero_beta_seven_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h0 : (actual p q 0).val = 1)
    (h1 : (actual p q 1).val = 1) (hq : q = (fun _ => 0))
    (hb : unitExponent p q = 7) : False := by
  obtain ⟨hc,hs,hf⟩ := root_four_profile (actual p q) h4
  rw [h0,h1] at hc hs hf
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have he := exponent_budget p q hn hG
  have ha : zeroExponent p = 4 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hP : totalP 6 p = 24 := by omega
  have hm := q_zero_moment p q hn hG hq
  rw [hf,hP] at hm
  norm_num at hm
  have hS : squares 6 p = 240 := by
    exact_mod_cast (by linarith : (squares 6 p : ℤ) = 240)
  have hcap (i : Fin 6) : p i ≤ 13 := by
    have hi := root_four_load_le_thirteen p q hn hG h4 i
    omega
  exact support_four_cap_thirteen_sum_twenty_four_square_240_impossible p
    (alpha_four_support_le_four p ha) hcap hP hS
#print axioms Paper7C61Four.root_four_one_two_one_three_qzero_beta_seven_impossible

end Paper7C61Four
