import Research.Backfill.Paper7.C61ThreeUnitWitness
import Research.Backfill.Paper7.C61ParameterSquares

/-! NEW SOURCE ONLY. Odd square sum and the three exact numerator identities
force a total at most eighteen when at most four actual sites are positive.
The proof uses congruences and position rotations, not a parameter table. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Parameters Paper7C61Three
open scoped BigOperators Classical

def PairNumerators (p : Fin 6 → ℕ) : Prop :=
  (4-(p 0 : ℤ))*(4-p 1)+(4-p 3)*(4-p 4) = 8 ∧
  (4-(p 1 : ℤ))*(4-p 2)+(4-p 4)*(4-p 5) = 8 ∧
  (4-(p 2 : ℤ))*(4-p 3)+(4-p 5)*(4-p 0) = 8
#print axioms Paper7C61Four.PairNumerators

theorem sum_shift_nat (f : Fin 6 → ℕ) :
    (∑ k, shiftSix f k) = ∑ k, f k := by
  simp only [Fin.sum_univ_six,shiftSix]
  change f 1+f 2+f 3+f 4+f 5+f 0 = f 0+f 1+f 2+f 3+f 4+f 5
  omega
#print axioms Paper7C61Four.sum_shift_nat

theorem totalP_shift (p : Fin 6 → ℕ) : totalP 6 (shiftSix p) = totalP 6 p := by
  exact sum_shift_nat p
#print axioms Paper7C61Four.totalP_shift

theorem support_shift (p : Fin 6 → ℕ) : (Kp 6 (shiftSix p)).card = (Kp 6 p).card := by
  have hcard (f : Fin 6 → ℕ) :
      (Kp 6 f).card = ∑ k : Fin 6, if 0 < f k then (1 : ℕ) else 0 := by
    simp only [Kp,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hcard,hcard]
  have h := sum_shift_nat (fun k => if 0 < p k then (1 : ℕ) else 0)
  exact h
#print axioms Paper7C61Four.support_shift

theorem pair_numerators_shift (p : Fin 6 → ℕ) (h : PairNumerators p) :
    PairNumerators (shiftSix p) := by
  obtain ⟨h0,h1,h2⟩ := h
  refine ⟨?_,?_,?_⟩
  · change (4-(p 1 : ℤ))*(4-p 2)+(4-p 4)*(4-p 5) = 8
    exact h1
  · change (4-(p 2 : ℤ))*(4-p 3)+(4-p 5)*(4-p 0) = 8
    exact h2
  · change (4-(p 3 : ℤ))*(4-p 4)+(4-p 0)*(4-p 1) = 8
    linarith only [h0]
#print axioms Paper7C61Four.pair_numerators_shift

theorem six_squares_remainder_three (a b c d e f : ℤ)
    (h : (a^2+b^2+c^2+d^2+e^2+f^2) % 4 = 3) :
    a%2+b%2+c%2+d%2+e%2+f%2 = 3 := by
  have ha := Int.sq_emod_four a
  have hb := Int.sq_emod_four b
  have hc := Int.sq_emod_four c
  have hd := Int.sq_emod_four d
  have he := Int.sq_emod_four e
  have hf := Int.sq_emod_four f
  omega
#print axioms Paper7C61Four.six_squares_remainder_three

theorem square_remainder_three_odd_count (p : Fin 6 → ℕ)
    (h : squares 6 p % 4 = 3) :
    (p 0 : ℤ)%2+(p 1 : ℤ)%2+(p 2 : ℤ)%2+
      (p 3 : ℤ)%2+(p 4 : ℤ)%2+(p 5 : ℤ)%2 = 3 := by
  have hs : ((squares 6 p : ℤ) % 4) = 3 := by exact_mod_cast h
  have he : (squares 6 p : ℤ) =
      (p 0 : ℤ)^2+(p 1 : ℤ)^2+(p 2 : ℤ)^2+
        (p 3 : ℤ)^2+(p 4 : ℤ)^2+(p 5 : ℤ)^2 := by
    simp [squares, Fin.sum_univ_succ]
    ring
  rw [he] at hs
  exact six_squares_remainder_three _ _ _ _ _ _ hs
#print axioms Paper7C61Four.square_remainder_three_odd_count

theorem opposite_pair_odd (a b c d : ℤ)
    (h : (4-a)*(4-b)+(4-c)*(4-d) = 8) (ha : a%2 = 1) (hb : b%2 = 1) :
    c%2 = 1 ∧ d%2 = 1 := by
  have hm := congrArg (fun z : ℤ => z%2) h
  constructor
  · by_contra hn
    have hc : c%2 = 0 := by omega
    norm_num [Int.add_emod, Int.mul_emod, Int.sub_emod, ha, hb, hc] at hm
  · by_contra hn
    have hd : d%2 = 0 := by omega
    norm_num [Int.add_emod, Int.mul_emod, Int.sub_emod, ha, hb, hd] at hm
#print axioms Paper7C61Four.opposite_pair_odd

theorem three_odds_no_adjacent (a b c d e f : ℤ)
    (hs : a%2+b%2+c%2+d%2+e%2+f%2 = 3)
    (hp : (4-a)*(4-b)+(4-d)*(4-e) = 8) : ¬ (a%2 = 1 ∧ b%2 = 1) := by
  rintro ⟨ha,hb⟩
  obtain ⟨hd,he⟩ := opposite_pair_odd a b d e hp ha hb
  omega
#print axioms Paper7C61Four.three_odds_no_adjacent

theorem pair_numerators_odd_alternation (p : Fin 6 → ℕ)
    (hs : (p 0 : ℤ)%2+(p 1 : ℤ)%2+(p 2 : ℤ)%2+
      (p 3 : ℤ)%2+(p 4 : ℤ)%2+(p 5 : ℤ)%2 = 3)
    (hp : PairNumerators p) :
    ((p 0 : ℤ)%2 = 1 ∧ (p 2 : ℤ)%2 = 1 ∧ (p 4 : ℤ)%2 = 1) ∨
      ((p 1 : ℤ)%2 = 1 ∧ (p 3 : ℤ)%2 = 1 ∧ (p 5 : ℤ)%2 = 1) := by
  have h01 := three_odds_no_adjacent (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) hs hp.1
  have h12 := three_odds_no_adjacent (p 1) (p 2) (p 3) (p 4) (p 5) (p 0)
    (by omega) hp.2.1
  have h23 := three_odds_no_adjacent (p 2) (p 3) (p 4) (p 5) (p 0) (p 1)
    (by omega) hp.2.2
  have h34 := three_odds_no_adjacent (p 3) (p 4) (p 5) (p 0) (p 1) (p 2)
    (by omega) (by linarith only [hp.1])
  have h45 := three_odds_no_adjacent (p 4) (p 5) (p 0) (p 1) (p 2) (p 3)
    (by omega) (by linarith only [hp.2.1])
  have h50 := three_odds_no_adjacent (p 5) (p 0) (p 1) (p 2) (p 3) (p 4)
    (by omega) (by linarith only [hp.2.2])
  omega
#print axioms Paper7C61Four.pair_numerators_odd_alternation

theorem support_four_three_positive_two_zeros (p : Fin 6 → ℕ)
    (hK : (Kp 6 p).card ≤ 4) (h0 : 0 < p 0) (h2 : 0 < p 2) (h4 : 0 < p 4) :
    (p 1 = 0 ∧ p 3 = 0) ∨ (p 3 = 0 ∧ p 5 = 0) ∨ (p 5 = 0 ∧ p 1 = 0) := by
  have hcount : (∑ k : Fin 6, if 0 < p k then (1 : ℕ) else 0) ≤ 4 := by
    have hcard : (Kp 6 p).card = ∑ k : Fin 6, if 0 < p k then (1 : ℕ) else 0 := by
      simp only [Kp,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [← hcard]
    exact hK
  rw [Fin.sum_univ_six] at hcount
  have h13 : ¬ (0 < p 1 ∧ 0 < p 3) := by
    rintro ⟨h1,h3⟩
    simp only [h0,h1,h2,h3,h4,ite_true] at hcount
    omega
  have h35 : ¬ (0 < p 3 ∧ 0 < p 5) := by
    rintro ⟨h3,h5⟩
    simp only [h0,h2,h3,h4,h5,ite_true] at hcount
    omega
  have h51 : ¬ (0 < p 5 ∧ 0 < p 1) := by
    rintro ⟨h5,h1⟩
    simp only [h0,h1,h2,h4,h5,ite_true] at hcount
    omega
  omega
#print axioms Paper7C61Four.support_four_three_positive_two_zeros

theorem two_zero_odd_middle_total_bound (p : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (ho2 : (p 2 : ℤ)%2 = 1)
    (hp : PairNumerators p) : totalP 6 p ≤ 18 := by
  obtain ⟨h0,h1,h2⟩ := hp
  norm_num only [hp1,hp3,Nat.cast_zero,sub_zero] at h0 h1 h2
  have hz : (4-(p 5 : ℤ))*((p 0 : ℤ)-p 4) = 0 := by nlinarith only [h1,h2]
  rcases mul_eq_zero.mp hz with hf | hae
  · have hf4 : (p 5 : ℤ) = 4 := by omega
    rw [hf4] at h1
    have hp2 : (p 2 : ℤ) = 2 := by nlinarith only [h1]
    rw [hp2] at ho2
    norm_num at ho2
  · have ha3 : (p 0 : ℤ) = 3 := by nlinarith only [h0,hae]
    have he3 : (p 4 : ℤ) = 3 := by nlinarith only [h0,hae]
    rw [he3] at h1
    have hlinear : 4*(p 2 : ℤ)+p 5 = 12 := by nlinarith only [h1]
    have hsum : (totalP 6 p : ℤ) =
        (p 0 : ℤ)+p 1+p 2+p 3+p 4+p 5 := by
      simp [totalP, Fin.sum_univ_succ]
      ring
    rw [hp1,hp3,ha3,he3] at hsum
    have hnonneg : (0 : ℤ) ≤ p 2 := Nat.cast_nonneg (p 2)
    have hbound : (totalP 6 p : ℤ) ≤ 18 := by omega
    exact_mod_cast hbound
#print axioms Paper7C61Four.two_zero_odd_middle_total_bound

theorem even_position_odds_total_bound (p : Fin 6 → ℕ)
    (hK : (Kp 6 p).card ≤ 4) (hp : PairNumerators p)
    (h0 : (p 0 : ℤ)%2 = 1) (h2 : (p 2 : ℤ)%2 = 1) (h4 : (p 4 : ℤ)%2 = 1) :
    totalP 6 p ≤ 18 := by
  have hp0 : 0 < p 0 := by omega
  have hp2 : 0 < p 2 := by omega
  have hp4 : 0 < p 4 := by omega
  rcases support_four_three_positive_two_zeros p hK hp0 hp2 hp4 with
    ⟨hp1,hp3⟩ | ⟨hp3,hp5⟩ | ⟨hp5,hp1⟩
  · exact two_zero_odd_middle_total_bound p hp1 hp3 h2 hp
  · let p2 := shiftSix (shiftSix p)
    have hm2 : PairNumerators p2 := pair_numerators_shift _ (pair_numerators_shift _ hp)
    have hb := two_zero_odd_middle_total_bound p2
      (by change p (3 : Fin 6) = 0; exact hp3)
      (by change p (5 : Fin 6) = 0; exact hp5)
      (by change (p (4 : Fin 6) : ℤ)%2 = 1; exact h4) hm2
    simpa only [p2,totalP_shift] using hb
  · let p4 := shiftSix (shiftSix (shiftSix (shiftSix p)))
    have hm4 : PairNumerators p4 := pair_numerators_shift _ (pair_numerators_shift _
      (pair_numerators_shift _ (pair_numerators_shift _ hp)))
    have hb := two_zero_odd_middle_total_bound p4
      (by change p (5 : Fin 6) = 0; exact hp5)
      (by change p (1 : Fin 6) = 0; exact hp1)
      (by change (p (0 : Fin 6) : ℤ)%2 = 1; exact h0) hm4
    simpa only [p4,totalP_shift] using hb
#print axioms Paper7C61Four.even_position_odds_total_bound

theorem support_four_odd_count_pair_total_bound (p : Fin 6 → ℕ)
    (hK : (Kp 6 p).card ≤ 4)
    (hs : (p 0 : ℤ)%2+(p 1 : ℤ)%2+(p 2 : ℤ)%2+
      (p 3 : ℤ)%2+(p 4 : ℤ)%2+(p 5 : ℤ)%2 = 3)
    (hp : PairNumerators p) : totalP 6 p ≤ 18 := by
  rcases pair_numerators_odd_alternation p hs hp with ⟨h0,h2,h4⟩ | ⟨h1,h3,h5⟩
  · exact even_position_odds_total_bound p hK hp h0 h2 h4
  · have hb := even_position_odds_total_bound (shiftSix p)
      (by rw [support_shift]; exact hK) (pair_numerators_shift p hp)
      (by change (p (1 : Fin 6) : ℤ)%2 = 1; exact h1)
      (by change (p (3 : Fin 6) : ℤ)%2 = 1; exact h3)
      (by change (p (5 : Fin 6) : ℤ)%2 = 1; exact h5)
    simpa only [totalP_shift] using hb
#print axioms Paper7C61Four.support_four_odd_count_pair_total_bound

end Paper7C61Four
