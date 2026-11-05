import Research.Backfill.Paper7.C61FourTraceConstraints

/-! NEW SOURCE ONLY. Scalar natural-number bounds from the trace equation. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four

theorem trace_small_coordinate_bound (a b c : ℕ) (ha : a ≤ 1)
    (h : (1 - (a : ℝ)) * (1 - (b : ℝ)) * (1 - (c : ℝ)) =
      5 - ((a : ℝ) + b + c)) :
    a + b + c ≤ 5 := by
  have hac : a = 0 ∨ a = 1 := by omega
  rcases hac with rfl | rfl
  · norm_num at h
    have hbcR : (b : ℝ) * c = 4 := by nlinarith only [h]
    have hbcN : b * c = 4 := by exact_mod_cast hbcR
    have hb : 1 ≤ b := by
      by_contra hn
      have hb0 : b = 0 := by omega
      simp [hb0] at hbcN
    have hc : 1 ≤ c := by
      by_contra hn
      have hc0 : c = 0 := by omega
      simp [hc0] at hbcN
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
    have hh := mul_nonneg (sub_nonneg.mpr hbR) (sub_nonneg.mpr hcR)
    have hsR : (b : ℝ) + c ≤ 5 := by nlinarith only [hbcR, hh]
    have hsN : b + c ≤ 5 := by exact_mod_cast hsR
    omega
  · norm_num at h
    have hsR : (1 : ℝ) + b + c ≤ 5 := by linarith
    exact_mod_cast hsR
#print axioms Paper7C61Four.trace_small_coordinate_bound

theorem trace_three_counts_le_seventeen (a b c : ℕ)
    (ha : a ≤ 13) (hb : b ≤ 13) (hc : c ≤ 13)
    (h : (1 - (a : ℝ)) * (1 - (b : ℝ)) * (1 - (c : ℝ)) =
      5 - ((a : ℝ) + b + c)) :
    a + b + c ≤ 17 := by
  by_cases ha1 : a ≤ 1
  · have := trace_small_coordinate_bound a b c ha1 h
    omega
  by_cases hb1 : b ≤ 1
  · have := trace_small_coordinate_bound b a c hb1 (by
      simpa only [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h)
    omega
  by_cases hc1 : c ≤ 1
  · have := trace_small_coordinate_bound c a b hc1 (by
      simpa only [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h)
    omega
  have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast (show 2 ≤ b by omega)
  have hc2 : (2 : ℝ) ≤ c := by exact_mod_cast (show 2 ≤ c by omega)
  have hab := mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2)
  have hac := mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hc2)
  have hbc := mul_nonneg (sub_nonneg.mpr hb2) (sub_nonneg.mpr hc2)
  have habc := mul_nonneg hab (sub_nonneg.mpr hc2)
  have hab0 : ((a : ℝ) - 2) * ((b : ℝ) - 2) = 0 := by
    nlinarith only [h, hab, hac, hbc, habc]
  have hac0 : ((a : ℝ) - 2) * ((c : ℝ) - 2) = 0 := by
    nlinarith only [h, hab, hac, hbc, habc]
  have hbc0 : ((b : ℝ) - 2) * ((c : ℝ) - 2) = 0 := by
    nlinarith only [h, hab, hac, hbc, habc]
  have habN : a = 2 ∨ b = 2 := by
    rcases mul_eq_zero.mp hab0 with hz | hz
    · exact Or.inl (by exact_mod_cast sub_eq_zero.mp hz)
    · exact Or.inr (by exact_mod_cast sub_eq_zero.mp hz)
  have hacN : a = 2 ∨ c = 2 := by
    rcases mul_eq_zero.mp hac0 with hz | hz
    · exact Or.inl (by exact_mod_cast sub_eq_zero.mp hz)
    · exact Or.inr (by exact_mod_cast sub_eq_zero.mp hz)
  have hbcN : b = 2 ∨ c = 2 := by
    rcases mul_eq_zero.mp hbc0 with hz | hz
    · exact Or.inl (by exact_mod_cast sub_eq_zero.mp hz)
    · exact Or.inr (by exact_mod_cast sub_eq_zero.mp hz)
  omega
#print axioms Paper7C61Four.trace_three_counts_le_seventeen

theorem sparse_trace_sum_twenty_three_impossible (a b c : ℕ)
    (hL : a + b + c = 23) (hab : a + b ≤ 13) (hc : c ≤ 13)
    (ht : (3 * (a : ℝ) + 4 * b) * ((c : ℝ) - 1) = 4 * c) : False := by
  have hc10 : (10 : ℝ) ≤ c := by exact_mod_cast (show 10 ≤ c by omega)
  have hc13 : (c : ℝ) ≤ 13 := by exact_mod_cast hc
  have hk : (30 : ℝ) ≤ 3 * a + 4 * b := by
    exact_mod_cast (show 30 ≤ 3 * a + 4 * b by omega)
  have hm : (30 : ℝ) * 9 ≤ (3 * (a : ℝ) + 4 * b) * ((c : ℝ) - 1) :=
    mul_le_mul hk (by linarith) (by norm_num) (by linarith)
  linarith
#print axioms Paper7C61Four.sparse_trace_sum_twenty_three_impossible

end Paper7C61Four
