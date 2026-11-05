import Research.Backfill.Paper7.C61SmallProfileLedger

set_option autoImplicit false
noncomputable section
namespace Paper7C61Small
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters
open scoped BigOperators Classical

theorem root_three_zero_twos_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (h0 : (actual p q 0).val = 0) : False := by
  obtain ⟨hc, hs, hf⟩ := root_three_profile (actual p q) h3
  rw [h0] at hc hs hf
  have hq := q_zero_of_card_le_two p q hn hG (by omega)
  have hQ : totalQ 6 q = 0 := by simp [hq, totalQ]
  have he := unitExponent_le_eight p q
  have ha := zeroExponent_le_six p
  have hb := exponent_budget p q hn hG
  have hbeta : unitExponent p q = 8 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hP : totalP 6 p = 5 := by omega
  have hm := q_zero_moment p q hn hG hq
  rw [hf,hP] at hm
  have hS : squares 6 p = 45 := by
    exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 45)
  have hbound := squares_le_total_square 6 p
  rw [hP,hS] at hbound
  norm_num at hbound
#print axioms Paper7C61Small.root_three_zero_twos_impossible

theorem root_three_one_two_data (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (h0 : (actual p q 0).val = 1) :
    q = (fun _ => 0) ∧ unitExponent p q = 8 ∧ totalP 6 p = 9 ∧
      squares 6 p = 45 ∧ ∃ k : Fin 6, p k = 6 ∧
        (∑ j ∈ Finset.univ.erase k, p j) = 3 ∧
        (∑ j ∈ Finset.univ.erase k, p j^2) = 9 := by
  obtain ⟨hc, hs, hf⟩ := root_three_profile (actual p q) h3
  rw [h0] at hc hs hf
  have hq := q_zero_of_card_le_two p q hn hG (by omega)
  have hQ : totalQ 6 q = 0 := by simp [hq, totalQ]
  have he := unitExponent_le_eight p q
  have ha := zeroExponent_le_six p
  have hb := exponent_budget p q hn hG
  have hsum := parameter_sum_eq_profile p q hn hG
  have hm := q_zero_moment p q hn hG hq
  rw [hf] at hm
  have hbeta : unitExponent p q = 8 := by
    by_contra h
    have he7 : unitExponent p q = 7 := by omega
    have hP : totalP 6 p = 8 := by omega
    have hS : squares 6 p = 48 := by
      rw [hP] at hm
      exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 48)
    exact no_sum8_square48 p hP hS
  have hP : totalP 6 p = 9 := by omega
  have hS : squares 6 p = 45 := by
    rw [hP] at hm
    exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 45)
  exact ⟨hq,hbeta,hP,hS,sum9_square45_maximum p hP hS⟩
#print axioms Paper7C61Small.root_three_one_two_data

theorem root_three_qpositive_data (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (hK : (Kq 6 q).Nonempty) :
    (actual p q 0).val = 2 ∧ unitExponent p q = 6 ∧ zeroExponent p = 6 ∧
      totalP 6 p + totalQ 6 q = 11 ∧
      squares 6 (fun k => p k+q k) + 2*totalQ 6 q = 51 ∧
      (Kp 6 p).card ≤ 3 ∧ (Kq 6 q).card ≤ 3 := by
  obtain ⟨hc, hs, hf⟩ := root_three_profile (actual p q) h3
  have hcard := nonempty_q_card_at_least_three p q hn hG hK
  have h0lt := (actual p q 0).isLt
  have h0 : (actual p q 0).val = 2 := by omega
  rw [h0] at hc hs hf
  have he := unitExponent_le_six_of_nonempty p q hK
  have ha := zeroExponent_le_six p
  have hb := exponent_budget p q hn hG
  have hbeta : unitExponent p q = 6 := by omega
  have halpha : zeroExponent p = 6 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hL : totalP 6 p + totalQ 6 q = 11 := by omega
  have hm := profile_parameter_moment p q hn hG
  rw [hf] at hm
  have hLZ : (totalP 6 p : ℤ) + totalQ 6 q = 11 := by exact_mod_cast hL
  have hS : squares 6 (fun k => p k+q k) + 2*totalQ 6 q = 51 := by
    exact_mod_cast (by norm_num at hm; linarith : (squares 6 (fun k => p k+q k) : ℤ) + 2*(totalQ 6 q : ℤ) = 51)
  have hqcard := q_support_le_profile p q hn hG
  exact ⟨h0,hbeta,halpha,hL,hS,alpha_six_support p halpha,by omega⟩
#print axioms Paper7C61Small.root_three_qpositive_data

theorem root_three_qpositive_total_bound (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (hK : (Kq 6 q).Nonempty) :
    1 ≤ totalQ 6 q ∧ totalQ 6 q ≤ 9 ∧ 2 ≤ totalP 6 p := by
  obtain ⟨_h0,_he,_ha,hL,hS,hpc,hqc⟩ := root_three_qpositive_data p q hn hG h3 hK
  have hp := support_cauchy 6 p
  have hq := support_cauchy 6 q
  change totalQ 6 q^2 ≤ (Kq 6 q).card * squares 6 q at hq
  have hp' : totalP 6 p^2 ≤ 3*squares 6 p :=
    hp.trans (Nat.mul_le_mul_right _ hpc)
  have hq' : totalQ 6 q^2 ≤ 3*squares 6 q :=
    hq.trans (Nat.mul_le_mul_right _ hqc)
  have hsplit := load_squares_split p q
  have hcs : totalP 6 p^2 + totalQ 6 q^2 ≤ 3*squares 6 (fun k => p k+q k) := by
    omega
  have hcsZ : (totalP 6 p : ℤ)^2 + (totalQ 6 q : ℤ)^2 ≤
      3*(squares 6 (fun k => p k+q k) : ℤ) := by exact_mod_cast hcs
  have hPZ : (totalP 6 p : ℤ) = 11-(totalQ 6 q : ℤ) := by omega
  have hSZ : (squares 6 (fun k => p k+q k) : ℤ) = 51-2*(totalQ 6 q : ℤ) := by omega
  rw [hPZ,hSZ] at hcsZ
  have hQ9 : totalQ 6 q ≤ 9 := by
    by_contra h
    have hQ10 : (10 : ℤ) ≤ totalQ 6 q := by omega
    have hmul := mul_nonneg (sub_nonneg.mpr hQ10) (Int.natCast_nonneg (totalQ 6 q))
    nlinarith
  have hpos := Finset.card_pos.mpr hK
  have hcard := Paper7Rank.support_card_le_sum 6 q
  change (Kq 6 q).card ≤ totalQ 6 q at hcard
  exact ⟨by omega,hQ9,by omega⟩
#print axioms Paper7C61Small.root_three_qpositive_total_bound

theorem root_three_qzero_two_twos_cases (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (h0 : (actual p q 0).val = 2)
    (hq : q = (fun _ => 0)) :
    (unitExponent p q = 6 ∧ totalP 6 p = 11 ∧ squares 6 p = 51) ∨
    (unitExponent p q = 7 ∧ totalP 6 p = 12 ∧ squares 6 p = 48) ∨
    (unitExponent p q = 8 ∧ totalP 6 p = 13 ∧ squares 6 p = 45) := by
  obtain ⟨_hc,hs,hf⟩ := root_three_profile (actual p q) h3
  rw [h0] at hs hf
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have hel := qzero_unitExponent_lower p q hq
  have heu := unitExponent_le_eight p q
  have hsum := parameter_sum_eq_profile p q hn hG
  have hm := q_zero_moment p q hn hG hq
  rw [hf] at hm
  have hcases : unitExponent p q = 6 ∨ unitExponent p q = 7 ∨ unitExponent p q = 8 := by omega
  rcases hcases with he | he | he
  · left
    have hP : totalP 6 p = 11 := by omega
    rw [hP] at hm
    refine ⟨he,hP,?_⟩
    exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 51)
  · right; left
    have hP : totalP 6 p = 12 := by omega
    rw [hP] at hm
    refine ⟨he,hP,?_⟩
    exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 48)
  · right; right
    have hP : totalP 6 p = 13 := by omega
    rw [hP] at hm
    refine ⟨he,hP,?_⟩
    exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 45)
#print axioms Paper7C61Small.root_three_qzero_two_twos_cases

end Paper7C61Small
