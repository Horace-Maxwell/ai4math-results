import Research.Backfill.Paper7.C61ThreeEvenMoments
import Research.Backfill.Paper7.C61AlphaSixParity
import Research.Backfill.Paper7.C61BetaEightSharpExclusions

/-! Complete original Perron-three zero-q branch. The parity and scaled
moment arguments use actual coordinates and ordinary monodromy. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Three
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61BetaEight
open scoped BigOperators Classical Matrix

theorem root_three_qzero_beta_six_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (hq : q = (fun _ => 0))
    (hb : unitExponent p q = 6) (hP : totalP 6 p = 11) : False := by
  have h0 := root_three_has_two_twos p q hn hG h3
  have hc := (root_three_profile (actual p q) h3).1
  have he := exponent_budget p q hn hG
  have ha : zeroExponent p = 6 := by omega
  have hpair := root_three_coefficient_pairs p q hn hG h3
  have hsum : p 0+p 1+p 2+p 3+p 4+p 5 = 11 := by
    simpa [totalP,Fin.sum_univ_succ,Nat.add_assoc] using hP
  have hsumR : (p 0 : ℝ)+p 1+p 2+p 3+p 4+p 5 = 11 := by exact_mod_cast hsum
  rcases alpha_six_parity p ha with ⟨hp1,hp3,hp5⟩ | ⟨hp0,hp2,hp4⟩
  · norm_num [coefficientTwo,hq,hp1,hp3,hp5] at hpair
    simp only [hp1,hp3,hp5,Nat.cast_zero] at hsumR
    nlinarith only [hpair.1,hpair.2.1,hpair.2.2,hsumR]
  · norm_num [coefficientTwo,hq,hp0,hp2,hp4] at hpair
    simp only [hp0,hp2,hp4,Nat.cast_zero] at hsumR
    nlinarith only [hpair.1,hpair.2.1,hpair.2.2,hsumR]
#print axioms Paper7C61Three.root_three_qzero_beta_six_impossible

theorem root_three_qzero_beta_seven_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (hq : q = (fun _ => 0))
    (hb : unitExponent p q = 7) (hP : totalP 6 p = 12)
    (hS : squares 6 p = 48) : False := by
  have h0 := root_three_has_two_twos p q hn hG h3
  have hc := (root_three_profile (actual p q) h3).1
  have he := exponent_budget p q hn hG
  have ha : zeroExponent p = 4 := by omega
  have hd := support_add_delta0_le_six p
  have hcard : (Kp 6 p).card ≤ 6 := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Kp 6 p))
  have hK : (Kp 6 p).card ≤ 4 := by unfold zeroExponent at ha; omega
  have hEven := support_four_square_multiple_eight_even p hK (by rw [hS]; norm_num)
  have hex (i : Fin 6) : ∃ n : ℕ, p i = 2*n := hEven i
  choose r hr using hex
  have hcap (i : Fin 6) : r i ≤ 3 := by
    have hi := root_three_load_le_six p q hn hG h3 i
    rw [hr i] at hi
    omega
  have hPscale : totalP 6 p = 2*totalP 6 r := by
    unfold totalP
    simp_rw [hr]
    exact (Finset.mul_sum _ _ _).symm
  have hSscale : squares 6 p = 4*squares 6 r := by
    calc
      _ = ∑ i : Fin 6, 4*r i^2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hr i]
        ring
      _ = 4*squares 6 r := (Finset.mul_sum _ _ _).symm
  have hrs : totalP 6 r = 6 := by omega
  have hrq : squares 6 r = 12 := by omega
  have hm := root_three_six_product p q hn hG h3
  have hcR (i : Fin 6) : coefficientTwo p q i = ((2-(r i : ℤ) : ℤ) : ℝ) := by
    rw [coefficientTwo,hq,hr i]
    push_cast
    ring
  have hmI : sixProduct (2-(r 0 : ℤ)) (2-(r 1 : ℤ)) (2-(r 2 : ℤ))
      (2-(r 3 : ℤ)) (2-(r 4 : ℤ)) (2-(r 5 : ℤ)) = 1 := by
    simpa only [hcR,realSixProduct,realTransfer,sixProduct,intTransfer] using hm
  exact sum_six_square_twelve_no_identity r hcap hrs hrq hmI
#print axioms Paper7C61Three.root_three_qzero_beta_seven_impossible

theorem root_three_qzero_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (hq : q = (fun _ => 0)) : False := by
  rcases Paper7C61Sharp.root_three_qzero_remaining_cases p q hn hG h3 hq with
    ⟨hb,hP,_hS⟩ | ⟨hb,hP,hS⟩
  · exact root_three_qzero_beta_six_impossible p q hn hG h3 hq hb hP
  · exact root_three_qzero_beta_seven_impossible p q hn hG h3 hq hb hP hS
#print axioms Paper7C61Three.root_three_qzero_impossible

end Paper7C61Three
