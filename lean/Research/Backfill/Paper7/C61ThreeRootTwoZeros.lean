import Research.Backfill.Paper7.C61ThreeMonodromy
import Research.Backfill.Paper7.C61ParameterSquares

/-! NEW SOURCE ONLY. A repeated root three, a cap of thirteen, and at most
four positive sites force either total twenty-four and square sum 192, or
total thirty-two with square sum different from 288. Actual zero positions
are retained and every cyclic distance is covered. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Three Paper7C61Parameters
open scoped BigOperators Matrix Classical

def unitThree (p : Fin 6 → ℕ) (k : Fin 6) : ℤ := 9-p k
#print axioms Paper7C61Four.unitThree

def TripleNumerators (p : Fin 6 → ℕ) : Prop :=
  ∀ k : Fin 6, unitThree p k*unitThree p (k+1)+
      unitThree p (k+3)*unitThree p (k+4) = 18 ∧
    9*unitThree p (k+4) = 9*(unitThree p k+unitThree p (k+2))-
      unitThree p k*unitThree p (k+1)*unitThree p (k+2)
#print axioms Paper7C61Four.TripleNumerators

theorem scaled_three_data (a b c d e f : ℤ)
    (h : realSixProduct ((a : ℝ)/3) ((b : ℝ)/3) ((c : ℝ)/3)
      ((d : ℝ)/3) ((e : ℝ)/3) ((f : ℝ)/3) = 1) :
    a*b+d*e = 18 ∧ 9*e = 9*(a+c)-a*b*c := by
  have ht := real_six_triple_data _ _ _ _ _ _ h
  have h1 : (a : ℝ)*b+(d : ℝ)*e = 18 := by nlinarith only [ht.1]
  have h2 : 9*(e : ℝ) = 9*((a : ℝ)+c)-(a : ℝ)*b*c := by
    nlinarith only [ht.2.2]
  exact ⟨by exact_mod_cast h1,by exact_mod_cast h2⟩
#print axioms Paper7C61Four.scaled_three_data

theorem mono_three_triple_numerators (p : Fin 6 → ℕ)
    (hm : Mono 6 p (fun _ => 0) 3 = 1) : TripleNumerators p := by
  have h : realSixProduct ((unitThree p 0 : ℝ)/3) ((unitThree p 1 : ℝ)/3)
      ((unitThree p 2 : ℝ)/3) ((unitThree p 3 : ℝ)/3)
      ((unitThree p 4 : ℝ)/3) ((unitThree p 5 : ℝ)/3) = 1 := by
    calc
      _ = Mono 6 p (fun _ => 0) 3 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [unitThree,Mono,Tk,fk,realSixProduct,realTransfer,List.finRange_succ] <;> ring
      _ = 1 := hm
  have h1 := real_six_rotate _ _ _ _ _ _ h
  have h2 := real_six_rotate _ _ _ _ _ _ h1
  have h3 := real_six_rotate _ _ _ _ _ _ h2
  have h4 := real_six_rotate _ _ _ _ _ _ h3
  have h5 := real_six_rotate _ _ _ _ _ _ h4
  intro k
  fin_cases k
  · exact scaled_three_data _ _ _ _ _ _ h
  · exact scaled_three_data _ _ _ _ _ _ h1
  · exact scaled_three_data _ _ _ _ _ _ h2
  · exact scaled_three_data _ _ _ _ _ _ h3
  · exact scaled_three_data _ _ _ _ _ _ h4
  · exact scaled_three_data _ _ _ _ _ _ h5
#print axioms Paper7C61Four.mono_three_triple_numerators

def turnThree (p : Fin 6 → ℕ) (c : Fin 6) : Fin 6 → ℕ := fun k => p (k+c)
#print axioms Paper7C61Four.turnThree

theorem triple_numerators_turn (p : Fin 6 → ℕ) (c : Fin 6) (h : TripleNumerators p) :
    TripleNumerators (turnThree p c) := by
  intro k
  simpa only [unitThree,turnThree,add_assoc,add_comm,add_left_comm] using h (k+c)
#print axioms Paper7C61Four.triple_numerators_turn

theorem totalP_turn_three (p : Fin 6 → ℕ) (c : Fin 6) :
    totalP 6 (turnThree p c) = totalP 6 p := by
  have hb : Function.Bijective (fun k : Fin 6 => k+c) :=
    ⟨fun _ _ h => add_right_cancel h,fun k => ⟨k-c,sub_add_cancel k c⟩⟩
  exact hb.sum_comp p
#print axioms Paper7C61Four.totalP_turn_three

theorem squares_turn_three (p : Fin 6 → ℕ) (c : Fin 6) :
    squares 6 (turnThree p c) = squares 6 p := by
  have hb : Function.Bijective (fun k : Fin 6 => k+c) :=
    ⟨fun _ _ h => add_right_cancel h,fun k => ⟨k-c,sub_add_cancel k c⟩⟩
  exact hb.sum_comp (fun k => p k^2)
#print axioms Paper7C61Four.squares_turn_three

theorem unit_three_interval (p : Fin 6 → ℕ) (hcap : ∀ k, p k ≤ 13) (k : Fin 6) :
    -4 ≤ unitThree p k ∧ unitThree p k ≤ 9 := by
  have hk := hcap k
  unfold unitThree
  omega
#print axioms Paper7C61Four.unit_three_interval

theorem interval_product_lower (a b : ℤ)
    (ha : -4 ≤ a ∧ a ≤ 9) (hb : -4 ≤ b ∧ b ≤ 9) : -36 ≤ a*b := by
  have h1 := mul_nonneg (show 0 ≤ a+4 by omega) (show 0 ≤ b+4 by omega)
  have h2 := mul_nonneg (show 0 ≤ 9-a by omega) (show 0 ≤ 9-b by omega)
  nlinarith only [h1,h2]
#print axioms Paper7C61Four.interval_product_lower

theorem not_int_square_eight (z : ℤ) (hz : z^2 = 8) : False := by
  have hp := Int.sq_emod_four z
  have he : z%2 = 0 := by omega
  obtain ⟨w,hw⟩ := Int.dvd_of_emod_eq_zero he
  rw [hw] at hz
  have hs : w^2 = 2 := by nlinarith only [hz]
  have hmod := Int.sq_emod_four w
  omega
#print axioms Paper7C61Four.not_int_square_eight

theorem not_int_square_sixty (z : ℤ) (hz : z^2 = 60) : False := by
  have hp := Int.sq_emod_four z
  have he : z%2 = 0 := by omega
  obtain ⟨w,hw⟩ := Int.dvd_of_emod_eq_zero he
  rw [hw] at hz
  have hs : w^2 = 15 := by nlinarith only [hz]
  have hmod := Int.sq_emod_four w
  omega
#print axioms Paper7C61Four.not_int_square_sixty

theorem triple_adjacent_zeros_impossible (p : Fin 6 → ℕ)
    (hcap : ∀ k, p k ≤ 13) (h : TripleNumerators p)
    (hz0 : p 0 = 0) (hz1 : p 1 = 0) : False := by
  have hp := (h 0).1
  change unitThree p 0*unitThree p 1+unitThree p 3*unitThree p 4 = 18 at hp
  have h0 : unitThree p 0 = 9 := by simp [unitThree,hz0]
  have h1 : unitThree p 1 = 9 := by simp [unitThree,hz1]
  rw [h0,h1] at hp
  have hb := interval_product_lower _ _ (unit_three_interval p hcap 3)
    (unit_three_interval p hcap 4)
  nlinarith only [hp,hb]
#print axioms Paper7C61Four.triple_adjacent_zeros_impossible

theorem triple_distance_two_cases (p : Fin 6 → ℕ)
    (hcap : ∀ k, p k ≤ 13) (h : TripleNumerators p)
    (hz0 : p 0 = 0) (hz2 : p 2 = 0) :
    (totalP 6 p = 24 ∧ squares 6 p = 192) ∨
      (totalP 6 p = 32 ∧ squares 6 p ≠ 288) := by
  have hU0 : unitThree p 0 = 9 := by simp [unitThree,hz0]
  have hU2 : unitThree p 2 = 9 := by simp [unitThree,hz2]
  have ht := (h 0).2
  change 9*unitThree p 4 = 9*(unitThree p 0+unitThree p 2)-
    unitThree p 0*unitThree p 1*unitThree p 2 at ht
  rw [hU0,hU2] at ht
  have hrel : unitThree p 4 = 18-9*unitThree p 1 := by nlinarith only [ht]
  have hb4 := unit_three_interval p hcap 4
  have hc : unitThree p 1 = 1 ∨ unitThree p 1 = 2 := by omega
  have hpair0 := (h 0).1
  change unitThree p 0*unitThree p 1+unitThree p 3*unitThree p 4 = 18 at hpair0
  have hpair2 := (h 2).1
  change unitThree p 2*unitThree p 3+unitThree p 5*unitThree p 0 = 18 at hpair2
  rcases hc with hU1 | hU1
  · have hU4 : unitThree p 4 = 9 := by omega
    rw [hU0,hU1,hU4] at hpair0
    have hU3 : unitThree p 3 = 1 := by nlinarith only [hpair0]
    rw [hU0,hU2,hU3] at hpair2
    have hU5 : unitThree p 5 = 1 := by nlinarith only [hpair2]
    have hp1 : p 1 = 8 := by unfold unitThree at hU1; omega
    have hp3 : p 3 = 8 := by unfold unitThree at hU3; omega
    have hp4 : p 4 = 0 := by unfold unitThree at hU4; omega
    have hp5 : p 5 = 8 := by unfold unitThree at hU5; omega
    left
    constructor <;> norm_num [totalP,squares,Fin.sum_univ_succ,
      hz0,hz2,hp1,hp3,hp4,hp5]
  · have hU4 : unitThree p 4 = 0 := by omega
    have hp1 : p 1 = 7 := by unfold unitThree at hU1; omega
    have hp4 : p 4 = 9 := by unfold unitThree at hU4; omega
    rw [hU0,hU2] at hpair2
    have hpair35 : p 3+p 5 = 16 := by
      unfold unitThree at hpair2
      omega
    right
    constructor
    · simp only [totalP,Fin.sum_univ_six,hz0,hz2,hp1,hp4]
      omega
    · intro hS
      have hsqN : p 3^2+p 5^2 = 158 := by
        norm_num [squares,Fin.sum_univ_succ,hz0,hz2,hp1,hp4] at hS
        omega
      have hsqZ : (p 3 : ℤ)^2+(p 5 : ℤ)^2 = 158 := by exact_mod_cast hsqN
      have hsumZ : (p 3 : ℤ)+p 5 = 16 := by exact_mod_cast hpair35
      have hsumSq : ((p 3 : ℤ)+p 5)^2 = 256 := by rw [hsumZ]; norm_num
      have hdiff : ((p 3 : ℤ)-p 5)^2 = 60 := by nlinarith only [hsqZ,hsumSq]
      exact not_int_square_sixty _ hdiff
#print axioms Paper7C61Four.triple_distance_two_cases

theorem opposed_pairs_square_288_impossible (a b c d : ℤ)
    (h1 : a+c = 16) (h2 : b+d = 16)
    (hm : (9-a)*(9-b)+(9-c)*(9-d) = 18)
    (hs : a^2+b^2+c^2+d^2 = 288) : False := by
  have hc : c = 16-a := by omega
  have hd : d = 16-b := by omega
  rw [hc,hd] at hm hs
  have hprod : (a-8)*(b-8) = 8 := by nlinarith only [hm]
  have hsq : (a-8)^2+(b-8)^2 = 16 := by nlinarith only [hs]
  have heqSq : ((a-8)-(b-8))^2 = 0 := by nlinarith only [hprod,hsq]
  have heq : a-8 = b-8 := sub_eq_zero.mp (sq_eq_zero_iff.mp heqSq)
  rw [← heq] at hprod
  have hz : (a-8)^2 = 8 := by nlinarith only [hprod]
  exact not_int_square_eight _ hz
#print axioms Paper7C61Four.opposed_pairs_square_288_impossible

theorem triple_opposite_zero_case (p : Fin 6 → ℕ) (h : TripleNumerators p)
    (hz0 : p 0 = 0) (hz3 : p 3 = 0) :
    totalP 6 p = 32 ∧ squares 6 p ≠ 288 := by
  have hU0 : unitThree p 0 = 9 := by simp [unitThree,hz0]
  have hU3 : unitThree p 3 = 9 := by simp [unitThree,hz3]
  have hpair0 := (h 0).1
  change unitThree p 0*unitThree p 1+unitThree p 3*unitThree p 4 = 18 at hpair0
  rw [hU0,hU3] at hpair0
  have hpair2 := (h 2).1
  change unitThree p 2*unitThree p 3+unitThree p 5*unitThree p 0 = 18 at hpair2
  rw [hU0,hU3] at hpair2
  have h14 : p 1+p 4 = 16 := by unfold unitThree at hpair0; omega
  have h25 : p 2+p 5 = 16 := by unfold unitThree at hpair2; omega
  constructor
  · simp only [totalP,Fin.sum_univ_six,hz0,hz3]
    omega
  · intro hS
    have hsqN : p 1^2+p 2^2+p 4^2+p 5^2 = 288 := by
      simpa [squares,Fin.sum_univ_succ,hz0,hz3,Nat.add_assoc] using hS
    have hsqZ : (p 1 : ℤ)^2+(p 2 : ℤ)^2+(p 4 : ℤ)^2+(p 5 : ℤ)^2 = 288 := by
      exact_mod_cast hsqN
    have h14Z : (p 1 : ℤ)+p 4 = 16 := by exact_mod_cast h14
    have h25Z : (p 2 : ℤ)+p 5 = 16 := by exact_mod_cast h25
    have hp := (h 1).1
    change (9-(p 1 : ℤ))*(9-(p 2 : ℤ))+
      (9-(p 4 : ℤ))*(9-(p 5 : ℤ)) = 18 at hp
    exact opposed_pairs_square_288_impossible _ _ _ _ h14Z h25Z hp hsqZ
#print axioms Paper7C61Four.triple_opposite_zero_case

theorem triple_zero_and_another_cases (p : Fin 6 → ℕ)
    (hcap : ∀ k, p k ≤ 13) (h : TripleNumerators p) (hz0 : p 0 = 0)
    (hz : ∃ k : Fin 6, k ≠ 0 ∧ p k = 0) :
    (totalP 6 p = 24 ∧ squares 6 p = 192) ∨
      (totalP 6 p = 32 ∧ squares 6 p ≠ 288) := by
  obtain ⟨k,hk0,hk⟩ := hz
  fin_cases k
  · exact (hk0 rfl).elim
  · exact (triple_adjacent_zeros_impossible p hcap h hz0 hk).elim
  · exact triple_distance_two_cases p hcap h hz0 hk
  · exact Or.inr (triple_opposite_zero_case p h hz0 hk)
  · change p (4 : Fin 6) = 0 at hk
    have hc := triple_distance_two_cases (turnThree p 4) (fun j => hcap (j+4))
      (triple_numerators_turn p 4 h)
      (by change p (4 : Fin 6) = 0; exact hk)
      (by change p (0 : Fin 6) = 0; exact hz0)
    simpa only [totalP_turn_three,squares_turn_three] using hc
  · change p (5 : Fin 6) = 0 at hk
    exact (triple_adjacent_zeros_impossible (turnThree p 5) (fun j => hcap (j+5))
      (triple_numerators_turn p 5 h)
      (by change p (5 : Fin 6) = 0; exact hk)
      (by change p (0 : Fin 6) = 0; exact hz0)).elim
#print axioms Paper7C61Four.triple_zero_and_another_cases

theorem triple_two_zero_cases (p : Fin 6 → ℕ)
    (hcap : ∀ k, p k ≤ 13) (h : TripleNumerators p)
    (hz : ∃ j k : Fin 6, j ≠ k ∧ p j = 0 ∧ p k = 0) :
    (totalP 6 p = 24 ∧ squares 6 p = 192) ∨
      (totalP 6 p = 32 ∧ squares 6 p ≠ 288) := by
  obtain ⟨j,k,hjk,hj,hk⟩ := hz
  have hz0 : turnThree p j 0 = 0 := by simpa only [turnThree,zero_add] using hj
  have hother : ∃ t : Fin 6, t ≠ 0 ∧ turnThree p j t = 0 := by
    refine ⟨k-j,?_,?_⟩
    · intro he
      exact hjk (sub_eq_zero.mp he).symm
    · simpa only [turnThree,sub_add_cancel] using hk
  have hc := triple_zero_and_another_cases (turnThree p j) (fun t => hcap (t+j))
    (triple_numerators_turn p j h) hz0 hother
  simpa only [totalP_turn_three,squares_turn_three] using hc
#print axioms Paper7C61Four.triple_two_zero_cases

theorem support_four_has_two_zeros (p : Fin 6 → ℕ) (hK : (Kp 6 p).card ≤ 4) :
    ∃ j k : Fin 6, j ≠ k ∧ p j = 0 ∧ p k = 0 := by
  have hc : 1 < ((Kp 6 p)ᶜ).card := by
    rw [Finset.card_compl,Fintype.card_fin]
    omega
  obtain ⟨j,hj,k,hk,hjk⟩ := Finset.one_lt_card.mp hc
  have hzero (i : Fin 6) (hi : i ∈ (Kp 6 p)ᶜ) : p i = 0 := by
    have hn := Finset.mem_compl.mp hi
    have hp : ¬ 0 < p i := by
      simpa only [Kp,Finset.mem_filter,Finset.mem_univ,true_and] using hn
    omega
  exact ⟨j,k,hjk,hzero j hj,hzero k hk⟩
#print axioms Paper7C61Four.support_four_has_two_zeros

theorem support_four_mono_three_moment_cases (p : Fin 6 → ℕ)
    (hcap : ∀ k, p k ≤ 13) (hK : (Kp 6 p).card ≤ 4)
    (hm : Mono 6 p (fun _ => 0) 3 = 1) :
    (totalP 6 p = 24 ∧ squares 6 p = 192) ∨
      (totalP 6 p = 32 ∧ squares 6 p ≠ 288) := by
  exact triple_two_zero_cases p hcap (mono_three_triple_numerators p hm)
    (support_four_has_two_zeros p hK)
#print axioms Paper7C61Four.support_four_mono_three_moment_cases

end Paper7C61Four
