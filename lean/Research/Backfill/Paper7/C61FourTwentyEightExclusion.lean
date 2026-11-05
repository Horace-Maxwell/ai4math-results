import Research.Backfill.Paper7.C61FourTwentyEightArithmetic
import Research.Backfill.Paper7.C61FourWithoutThreeQzero
import Research.Backfill.Paper7.C61FinSixIndexSimp

/-! NEW SOURCE ONLY. The zero-q profile {2,2,3,4}, including the entire
beta-seven position domain, without a tuple enumeration or coverage premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Three
open scoped BigOperators Classical

theorem mono_two_qzero_shift (p : Fin 6 → ℕ)
    (hm : Mono 6 p (fun _ => 0) 2 = 1) : Mono 6 (shiftSix p) (fun _ => 0) 2 = 1 := by
  rw [mono_two_six_product] at hm ⊢
  have hr := real_six_rotate _ _ _ _ _ _ hm
  simpa [coefficientTwo,shiftSix] using hr
#print axioms Paper7C61Four.mono_two_qzero_shift

def TwentyEightData (p : Fin 6 → ℕ) : Prop :=
  totalP 6 p = 28 ∧ squares 6 p = 240 ∧ (∀ k, p k ≤ 13) ∧
    Mono 6 p (fun _ => 0) 2 = 1
#print axioms Paper7C61Four.TwentyEightData

theorem twenty_eight_data_shift (p : Fin 6 → ℕ) (h : TwentyEightData p) :
    TwentyEightData (shiftSix p) := by
  obtain ⟨hP,hS,hcap,hm⟩ := h
  refine ⟨by rw [totalP_shift]; exact hP,?_,fun k => hcap (k+1),
    mono_two_qzero_shift p hm⟩
  have hs := sum_shift_nat (fun k => p k^2)
  have he : squares 6 (shiftSix p) = squares 6 p := by
    simpa only [squares,shiftSix] using hs
  exact he.trans hS
#print axioms Paper7C61Four.twenty_eight_data_shift

theorem twenty_eight_head_zero_impossible (p : Fin 6 → ℕ)
    (hz : p 0 = 0) (h : TwentyEightData p) : False := by
  obtain ⟨hP,hS,hcap,hm⟩ := h
  have hn := mono_two_pair_numerators p hm
  rw [mono_two_six_product] at hm
  have ht := real_six_triple_data _ _ _ _ _ _ hm
  have hr : coefficientTwo p (fun _ => 0) 2 = coefficientTwo p (fun _ => 0) 0 +
      coefficientTwo p (fun _ => 0) 4 - coefficientTwo p (fun _ => 0) 0 *
        coefficientTwo p (fun _ => 0) 5 * coefficientTwo p (fun _ => 0) 4 := by
    linear_combination -ht.2.2 + coefficientTwo p (fun _ => 0) 0 * ht.2.1
  have hpoly := ht.2.2
  norm_num [coefficientTwo,hz] at hpoly hr
  have hE : (p 4 : ℤ) = ((p 1 : ℤ)-3)*((p 2 : ℤ)-4) := by
    exact_mod_cast (by nlinarith only [hpoly] :
      (p 4 : ℝ) = ((p 1 : ℝ)-3)*((p 2 : ℝ)-4))
  have hC : (p 2 : ℤ) = ((p 5 : ℤ)-3)*((p 4 : ℤ)-4) := by
    exact_mod_cast (by nlinarith only [hr] :
      (p 2 : ℝ) = ((p 5 : ℝ)-3)*((p 4 : ℝ)-4))
  have hDE : (4-(p 3 : ℤ))*(4-(p 4 : ℤ)) = 4*(p 1 : ℤ)-8 := by
    have hi := hn.1
    norm_num [hz] at hi
    nlinarith only [hi]
  have hCD : (4-(p 2 : ℤ))*(4-(p 3 : ℤ)) = 4*(p 5 : ℤ)-8 := by
    have hi := hn.2.2
    norm_num [hz] at hi
    nlinarith only [hi]
  have hs : (p 1 : ℤ)+p 2+p 3+p 4+p 5 = 28 := by
    exact_mod_cast (by simpa [totalP,Fin.sum_univ_succ,hz,Nat.add_assoc] using hP :
      p 1+p 2+p 3+p 4+p 5 = 28)
  have hq : (p 1 : ℤ)^2+(p 2 : ℤ)^2+(p 3 : ℤ)^2+(p 4 : ℤ)^2+(p 5 : ℤ)^2 = 240 := by
    exact_mod_cast (by simpa [squares,Fin.sum_univ_succ,hz,Nat.add_assoc] using hS :
      p 1^2+p 2^2+p 3^2+p 4^2+p 5^2 = 240)
  exact five_head_zero_moment_obstruction (p 1) (p 2) (p 3) (p 4) (p 5)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hcap 3) hs hq hE hC hDE hCD
#print axioms Paper7C61Four.twenty_eight_head_zero_impossible

theorem twenty_eight_zero_impossible (p : Fin 6 → ℕ)
    (hz : ∃ j, p j = 0) (h : TwentyEightData p) : False := by
  let p1 := shiftSix p
  let p2 := shiftSix p1
  let p3 := shiftSix p2
  let p4 := shiftSix p3
  let p5 := shiftSix p4
  have h1 : TwentyEightData p1 := twenty_eight_data_shift p h
  have h2 : TwentyEightData p2 := twenty_eight_data_shift p1 h1
  have h3 : TwentyEightData p3 := twenty_eight_data_shift p2 h2
  have h4 : TwentyEightData p4 := twenty_eight_data_shift p3 h3
  have h5 : TwentyEightData p5 := twenty_eight_data_shift p4 h4
  obtain ⟨j,hj⟩ := hz
  fin_cases j
  · exact twenty_eight_head_zero_impossible p hj h
  · apply twenty_eight_head_zero_impossible p1 _ h1
    change p (1 : Fin 6) = 0 at hj
    simpa [p1,shiftSix] using hj
  · apply twenty_eight_head_zero_impossible p2 _ h2
    change p (2 : Fin 6) = 0 at hj
    simpa [p2,p1,shiftSix] using hj
  · apply twenty_eight_head_zero_impossible p3 _ h3
    change p (3 : Fin 6) = 0 at hj
    simpa [p3,p2,p1,shiftSix] using hj
  · apply twenty_eight_head_zero_impossible p4 _ h4
    change p (4 : Fin 6) = 0 at hj
    simpa [p4,p3,p2,p1,shiftSix] using hj
  · apply twenty_eight_head_zero_impossible p5 _ h5
    change p (5 : Fin 6) = 0 at hj
    simpa [p5,p4,p3,p2,p1,shiftSix] using hj
#print axioms Paper7C61Four.twenty_eight_zero_impossible

theorem root_four_two_twos_one_three_qzero_beta_seven_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h0 : (actual p q 0).val = 2)
    (h1 : (actual p q 1).val = 1) (hq : q = (fun _ => 0))
    (hb : unitExponent p q = 7) : False := by
  obtain ⟨hc,hs,hf⟩ := root_four_profile (actual p q) h4
  rw [h0,h1] at hc hs hf
  have he := exponent_budget p q hn hG
  have ha : zeroExponent p = 2 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have hP : totalP 6 p = 28 := by omega
  have hmom := q_zero_moment p q hn hG hq
  rw [hf,hP] at hmom
  have hS : squares 6 p = 240 := by
    exact_mod_cast (by norm_num at hmom; linarith : (squares 6 p : ℤ) = 240)
  have hKbound := support_add_delta0_le_six p
  have hKsix : (Kp 6 p).card ≤ 6 := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Kp 6 p))
  have hKfive : (Kp 6 p).card ≤ 5 := by unfold zeroExponent at ha; omega
  have hz : ∃ j, p j = 0 := by
    by_contra! hp
    have heq : Kp 6 p = Finset.univ := by
      ext j
      simp only [Kp,Finset.mem_filter,Finset.mem_univ,true_and]
      exact iff_true_intro (Nat.pos_of_ne_zero (hp j))
    rw [heq] at hKfive
    norm_num at hKfive
  have hcap (k : Fin 6) : p k ≤ 13 := by
    have hi := Paper7C61Higher.root_four_load_le_thirteen p q hn hG h4 k
    omega
  exact twenty_eight_zero_impossible p hz ⟨hP,hS,hcap,
    by simpa only [hq] using actual_two_monodromy p q h0⟩
#print axioms Paper7C61Four.root_four_two_twos_one_three_qzero_beta_seven_impossible

end Paper7C61Four
