import Research.Backfill.Paper7.C61PairSumSigns

/-! NEW SOURCE ONLY. The three signs, including zero, are handled analytically
over the full natural-number domain; no bounded parameter tuple table is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four

def oddTwoCoefficient (n : ℕ) : ℝ := 2-2*(n : ℝ)/3
#print axioms Paper7C61Four.oddTwoCoefficient

theorem odd_two_discrete_sign (n : ℕ) :
    oddTwoCoefficient n = 0 ∨ 2/3 ≤ oddTwoCoefficient n ∨ oddTwoCoefficient n ≤ -2/3 := by
  have hc : n ≤ 2 ∨ n = 3 ∨ 4 ≤ n := by omega
  rcases hc with hn | rfl | hn
  · right; left
    have hnR : (n : ℝ) ≤ 2 := by exact_mod_cast hn
    unfold oddTwoCoefficient
    linarith
  · left; norm_num [oddTwoCoefficient]
  · right; right
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    unfold oddTwoCoefficient
    linarith
#print axioms Paper7C61Four.odd_two_discrete_sign

theorem odd_two_le_two (n : ℕ) : oddTwoCoefficient n ≤ 2 := by
  unfold oddTwoCoefficient
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith
#print axioms Paper7C61Four.odd_two_le_two

theorem odd_two_negative_q_ge_four (n : ℕ) (h : oddTwoCoefficient n ≤ -2/3) : 4 ≤ n := by
  unfold oddTwoCoefficient at h
  have hnR : (4 : ℝ) ≤ n := by linarith
  exact_mod_cast hnR
#print axioms Paper7C61Four.odd_two_negative_q_ge_four

theorem pair_two_total_twenty_six_impossible (a c e : ℝ) (i j k Qe : ℕ)
    (hQ : Qe+i+j+k ≤ 10)
    (hS : a+c+e = -7+((i : ℝ)+j+k)/2-(Qe : ℝ)/6)
    (h0 : a*oddTwoCoefficient i+e*oddTwoCoefficient j=2)
    (h1 : c*oddTwoCoefficient i+e*oddTwoCoefficient k=2)
    (h2 : c*oddTwoCoefficient j+a*oddTwoCoefficient k=2) : False := by
  let x := oddTwoCoefficient i
  let y := oddTwoCoefficient j
  let z := oddTwoCoefficient k
  change a*x+e*y=2 at h0
  change c*x+e*z=2 at h1
  change c*y+a*z=2 at h2
  have hQR : (Qe : ℝ)+i+j+k ≤ 10 := by exact_mod_cast hQ
  have hQe : (0 : ℝ) ≤ Qe := Nat.cast_nonneg Qe
  have hupper : a+c+e ≤ -2 := by linarith
  have hBsum : -2/3 ≤ x+y+z := by
    dsimp [x, y, z, oddTwoCoefficient]
    linarith
  have hLower : 8 ≤ i+j+k → -10/3 ≤ a+c+e := by
    intro hn
    have hR : (8 : ℝ) ≤ (i : ℝ)+j+k := by exact_mod_cast hn
    linarith
  by_cases hx0 : x = 0
  · have hp := pair_zero_coefficient_sum_positive a c e x y z hx0 hBsum
      (odd_two_discrete_sign j) h0 h1 h2
    linarith
  by_cases hy0 : y = 0
  · have hp := pair_zero_coefficient_sum_positive c e a y z x hy0 (by linarith)
      (odd_two_discrete_sign k) h2 (by nlinarith only [h0]) (by nlinarith only [h1])
    linarith
  by_cases hz0 : z = 0
  · have hp := pair_zero_coefficient_sum_positive e a c z x y hz0 (by linarith)
      (odd_two_discrete_sign i) (by nlinarith only [h1])
      (by nlinarith only [h2]) h0
    linarith
  have hxS : 2/3 ≤ x ∨ x ≤ -2/3 := by
    rcases odd_two_discrete_sign i with hi | hi | hi
    · exact (hx0 hi).elim
    · exact Or.inl hi
    · exact Or.inr hi
  have hyS : 2/3 ≤ y ∨ y ≤ -2/3 := by
    rcases odd_two_discrete_sign j with hj | hj | hj
    · exact (hy0 hj).elim
    · exact Or.inl hj
    · exact Or.inr hj
  have hzS : 2/3 ≤ z ∨ z ≤ -2/3 := by
    rcases odd_two_discrete_sign k with hk | hk | hk
    · exact (hz0 hk).elim
    · exact Or.inl hk
    · exact Or.inr hk
  have hx2 : x ≤ 2 := odd_two_le_two i
  have hy2 : y ≤ 2 := odd_two_le_two j
  have hz2 : z ≤ 2 := odd_two_le_two k
  have hprod := alternating_pair_sum_product a c e x y z h0 h1 h2
  rcases hxS with hx | hx
  · rcases hyS with hy | hy
    · rcases hzS with hz | hz
      · have hp := pair_sum_all_positive (a+c+e) x y z hx hy hz hx2 hy2 hz2 hprod
        linarith
      · have hp := pair_sum_one_negative (a+c+e) z x y (by linarith) (by linarith)
          (by linarith) (by nlinarith only [hprod])
        linarith
    · rcases hzS with hz | hz
      · have hp := pair_sum_one_negative (a+c+e) y x z (by linarith) (by linarith)
          (by linarith) (by nlinarith only [hprod])
        linarith
      · have hp := pair_sum_two_negative (a+c+e) y z x hy hz (by linarith) hx2
          (by linarith) (by nlinarith only [hprod])
        have hj := odd_two_negative_q_ge_four j hy
        have hk := odd_two_negative_q_ge_four k hz
        have hl := hLower (by omega)
        linarith
  · rcases hyS with hy | hy
    · rcases hzS with hz | hz
      · have hp := pair_sum_one_negative (a+c+e) x y z (by linarith) (by linarith)
          (by linarith) hprod
        linarith
      · have hp := pair_sum_two_negative (a+c+e) x z y hx hz (by linarith) hy2
          (by linarith) (by nlinarith only [hprod])
        have hi := odd_two_negative_q_ge_four i hx
        have hk := odd_two_negative_q_ge_four k hz
        have hl := hLower (by omega)
        linarith
    · rcases hzS with hz | hz
      · have hp := pair_sum_two_negative (a+c+e) x y z hx hy (by linarith) hz2 hBsum hprod
        have hi := odd_two_negative_q_ge_four i hx
        have hj := odd_two_negative_q_ge_four j hy
        have hl := hLower (by omega)
        linarith
      · linarith
#print axioms Paper7C61Four.pair_two_total_twenty_six_impossible

end Paper7C61Four
