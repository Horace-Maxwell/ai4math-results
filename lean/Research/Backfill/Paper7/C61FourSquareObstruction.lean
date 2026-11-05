import Mathlib

/-! Source-only divisibility obstruction. No finite residue enumeration. -/
set_option autoImplicit false
namespace Paper7C61Sparse

/-- Four integer squares summing to a multiple of eight have even bases. -/
theorem four_squares_eight_divides_even (a b c d : ℤ)
    (h : 8 ∣ a^2 + b^2 + c^2 + d^2) :
    2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ 2 ∣ d := by
  have h4 : (a^2 + b^2 + c^2 + d^2) % 4 = 0 :=
    Int.emod_eq_zero_of_dvd (dvd_trans (by norm_num : (4 : ℤ) ∣ 8) h)
  have ha := Int.sq_emod_four a
  have hb := Int.sq_emod_four b
  have hc := Int.sq_emod_four c
  have hd := Int.sq_emod_four d
  have hcases :
      (a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0) ∨
      (a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 ∧ d % 2 = 1) := by omega
  rcases hcases with ⟨ha0,hb0,hc0,hd0⟩ | ⟨ha1,hb1,hc1,hd1⟩
  · exact ⟨Int.dvd_of_emod_eq_zero ha0, Int.dvd_of_emod_eq_zero hb0,
      Int.dvd_of_emod_eq_zero hc0, Int.dvd_of_emod_eq_zero hd0⟩
  · obtain ⟨u, hu⟩ := Int.eight_dvd_sq_sub_one_of_odd (Int.odd_iff.mpr ha1)
    obtain ⟨v, hv⟩ := Int.eight_dvd_sq_sub_one_of_odd (Int.odd_iff.mpr hb1)
    obtain ⟨w, hw⟩ := Int.eight_dvd_sq_sub_one_of_odd (Int.odd_iff.mpr hc1)
    obtain ⟨t, ht⟩ := Int.eight_dvd_sq_sub_one_of_odd (Int.odd_iff.mpr hd1)
    obtain ⟨k, hk⟩ := h
    omega
#print axioms Paper7C61Sparse.four_squares_eight_divides_even

/-- Two divisions by four in the square sum force an impossible parity
relation: the final coordinate sum is nine but the square sum is thirty-six. -/
theorem four_no_sum36_square576 (a b c d : ℤ)
    (hs : a+b+c+d = 36) (hq : a^2+b^2+c^2+d^2 = 576) : False := by
  obtain ⟨ha,hb,hc,hd⟩ := four_squares_eight_divides_even a b c d (by rw [hq]; norm_num)
  obtain ⟨a',rfl⟩ := ha
  obtain ⟨b',rfl⟩ := hb
  obtain ⟨c',rfl⟩ := hc
  obtain ⟨d',rfl⟩ := hd
  have hs' : a'+b'+c'+d' = 18 := by linarith
  have hq' : a'^2+b'^2+c'^2+d'^2 = 144 := by nlinarith [hq]
  obtain ⟨ha,hb,hc,hd⟩ := four_squares_eight_divides_even a' b' c' d' (by rw [hq']; norm_num)
  obtain ⟨a'',rfl⟩ := ha
  obtain ⟨b'',rfl⟩ := hb
  obtain ⟨c'',rfl⟩ := hc
  obtain ⟨d'',rfl⟩ := hd
  have hs'' : a''+b''+c''+d'' = 9 := by linarith
  have hq'' : a''^2+b''^2+c''^2+d''^2 = 36 := by nlinarith [hq']
  have ha := Int.sq_emod_four a''
  have hb := Int.sq_emod_four b''
  have hc := Int.sq_emod_four c''
  have hd := Int.sq_emod_four d''
  omega
#print axioms Paper7C61Sparse.four_no_sum36_square576

end Paper7C61Sparse
