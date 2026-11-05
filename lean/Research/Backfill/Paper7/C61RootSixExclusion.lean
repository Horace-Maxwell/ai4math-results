import Research.Backfill.Paper7.C61ParameterSquares

/-! Both Perron-six spectral possibilities are excluded by complete moments
and integer square inequalities, without enumerating parameter tuples. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Parameters
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile
open scoped BigOperators Classical

theorem q_zero_of_card_le_two (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (hc : card (actual p q) ≤ 2) :
    q = (fun _ => 0) := by
  by_cases hK : (Kq 6 q).Nonempty
  · have h := nonempty_q_card_at_least_three p q hn hG hK
    omega
  · have he := Finset.not_nonempty_iff_eq_empty.mp hK
    exact zero_of_totalQ_zero 6 q (Paper7Rank.support_sum_zero 6 q he)
#print axioms Paper7C61Parameters.q_zero_of_card_le_two

theorem q_zero_moment (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (hq : q = (fun _ => 0)) :
    fourth (actual p q) = (squares 6 p : ℤ) + 3 * (totalP 6 p : ℤ) + 12 := by
  have h := profile_parameter_moment p q hn hG
  simpa [hq, totalQ] using h
#print axioms Paper7C61Parameters.q_zero_moment

theorem exclude_six_only (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q))
    (hc : card (actual p q) = 1) (hs : square (actual p q) = 36)
    (hf : fourth (actual p q) = 1260) : False := by
  have hq := q_zero_of_card_le_two p q hn hG (by omega)
  have hQ : totalQ 6 q = 0 := by simp [hq, totalQ]
  have hb := exponent_budget p q hn hG
  have ha := zeroExponent_le_six p
  have he := unitExponent_le_eight p q
  have hbeta : unitExponent p q = 8 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hP : totalP 6 p = 32 := by omega
  have hm := q_zero_moment p q hn hG hq
  rw [hf, hP] at hm
  norm_num at hm
  have hS : squares 6 p = 1152 := by
    exact_mod_cast (by linarith : (squares 6 p : ℤ) = 1152)
  have hbound := squares_le_total_square 6 p
  rw [hP, hS] at hbound
  omega
#print axioms Paper7C61Parameters.exclude_six_only

theorem exclude_six_two (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q))
    (hc : card (actual p q) = 2) (hs : square (actual p q) = 40)
    (hf : fourth (actual p q) = 1272) : False := by
  have hq := q_zero_of_card_le_two p q hn hG (by omega)
  have hQ : totalQ 6 q = 0 := by simp [hq, totalQ]
  have hb := exponent_budget p q hn hG
  have ha := zeroExponent_le_six p
  have he := unitExponent_le_eight p q
  have hsum := parameter_sum_eq_profile p q hn hG
  have hbeta : unitExponent p q = 7 ∨ unitExponent p q = 8 := by omega
  have hm := q_zero_moment p q hn hG hq
  rw [hf] at hm
  rcases hbeta with he7 | he8
  · have hP : totalP 6 p = 35 := by omega
    have hS : squares 6 p = 1155 := by
      rw [hP] at hm
      norm_num at hm
      exact_mod_cast (by linarith : (squares 6 p : ℤ) = 1155)
    exact no_sum35_square1155 p hP hS
  · have hP : totalP 6 p = 36 := by omega
    have hS : squares 6 p = 1152 := by
      rw [hP] at hm
      norm_num at hm
      exact_mod_cast (by linarith : (squares 6 p : ℤ) = 1152)
    exact no_sum36_square1152 p hP hS
#print axioms Paper7C61Parameters.exclude_six_two

theorem actual_six_zero (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : (actual p q 4).val = 0 := by
  have hshape := actual_shapes p q hp hn hG
  rcases hshape with ⟨_h1, _h2, _h3, h4⟩ | ⟨_h2, _h3, h4⟩ |
    ⟨_h3, h4, _hh⟩ | ⟨h4, h3, h2, h1, h0⟩
  · exact h4
  · exact h4
  · exact h4
  · exfalso
    have hcases : (actual p q 0).val = 0 ∨ (actual p q 0).val = 1 := by omega
    rcases hcases with h0z | h0o
    · apply exclude_six_only p q hn hG
      · norm_num [card, Fin.sum_univ_succ, h0z, h1, h2, h3, h4]
      · norm_num [square, value, Fin.sum_univ_succ, h0z, h1, h2, h3, h4]
      · norm_num [fourth, value, Fin.sum_univ_succ, h0z, h1, h2, h3, h4]
    · apply exclude_six_two p q hn hG
      · norm_num [card, Fin.sum_univ_succ, h0o, h1, h2, h3, h4]
      · norm_num [square, value, Fin.sum_univ_succ, h0o, h1, h2, h3, h4]
      · norm_num [fourth, value, Fin.sum_univ_succ, h0o, h1, h2, h3, h4]
#print axioms Paper7C61Parameters.actual_six_zero

end Paper7C61Parameters
