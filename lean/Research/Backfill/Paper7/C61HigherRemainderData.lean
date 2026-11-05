import Research.Backfill.Paper7.C61PerronFiveTwoTwos

/-! Exact necessary parameter identities for the still-open branches.
These are reductions with proof bodies, not completed classifications. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Higher
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small
open scoped BigOperators Classical

theorem root_four_parameter_relations (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) :
    totalP 6 p + totalQ 6 q =
        4 * (actual p q 0).val + 9 * (actual p q 1).val + unitExponent p q + 4 ∧
      squares 6 (fun k => p k + q k) + 2 * totalQ 6 q + 3 * unitExponent p q =
        45 * (actual p q 1).val + 216 := by
  obtain ⟨_hc, hs, hf⟩ := root_four_profile (actual p q) h4
  have hsum := parameter_sum_eq_profile p q hn hG
  rw [hs] at hsum
  have hL : totalP 6 p + totalQ 6 q =
      4 * (actual p q 0).val + 9 * (actual p q 1).val + unitExponent p q + 4 := by omega
  have hLZ : (totalP 6 p : ℤ) + totalQ 6 q =
      4 * ((actual p q 0).val : ℤ) + 9 * ((actual p q 1).val : ℤ) +
        (unitExponent p q : ℤ) + 4 := by exact_mod_cast hL
  have hm := profile_parameter_moment p q hn hG
  rw [hf] at hm
  refine ⟨hL, ?_⟩
  exact_mod_cast (by linarith :
    (squares 6 (fun k => p k + q k) : ℤ) + 2 * (totalQ 6 q : ℤ) +
      3 * (unitExponent p q : ℤ) = 45 * ((actual p q 1).val : ℤ) + 216)
#print axioms Paper7C61Higher.root_four_parameter_relations

theorem root_five_three_parameter_relations (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h1 : (actual p q 1).val = 1)
    (h2 : (actual p q 2).val = 0) :
    totalP 6 p + totalQ 6 q = 4 * (actual p q 0).val + unitExponent p q + 22 ∧
      squares 6 (fun k => p k + q k) + 2 * totalQ 6 q + 3 * unitExponent p q = 594 := by
  obtain ⟨_hc, hs, hf⟩ := root_five_profile (actual p q) h5
  rw [h1, h2] at hs hf
  have hsum := parameter_sum_eq_profile p q hn hG
  rw [hs] at hsum
  have hL : totalP 6 p + totalQ 6 q =
      4 * (actual p q 0).val + unitExponent p q + 22 := by omega
  have hLZ : (totalP 6 p : ℤ) + totalQ 6 q =
      4 * ((actual p q 0).val : ℤ) + (unitExponent p q : ℤ) + 22 := by exact_mod_cast hL
  have hm := profile_parameter_moment p q hn hG
  rw [hf] at hm
  norm_num at hm
  refine ⟨hL, ?_⟩
  exact_mod_cast (by linarith :
    (squares 6 (fun k => p k + q k) : ℤ) + 2 * (totalQ 6 q : ℤ) +
      3 * (unitExponent p q : ℤ) = 594)
#print axioms Paper7C61Higher.root_five_three_parameter_relations

/-- The four-entry Perron-five branch leaves exactly these necessary
parameter domains. Neither domain is claimed impossible here. -/
theorem root_five_three_two_twos_data (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 2)
    (h1 : (actual p q 1).val = 1) (h2 : (actual p q 2).val = 0) :
    (q = (fun _ => 0) ∧ unitExponent p q = 6 ∧ zeroExponent p = 4 ∧
      totalP 6 p = 36 ∧ squares 6 p = 576 ∧ (Kp 6 p).card ≤ 4) ∨
    (totalQ 6 q = 1 ∧ unitExponent p q = 5 ∧ zeroExponent p = 6 ∧
      totalP 6 p = 34 ∧ squares 6 (fun k => p k + q k) = 577 ∧
        (Kp 6 p).card ≤ 3) := by
  have hc := (root_five_profile (actual p q) h5).1
  rw [h0, h1, h2] at hc
  obtain ⟨hL, hm⟩ := root_five_three_parameter_relations p q hn hG h5 h1 h2
  rw [h0] at hL
  have hb := exponent_budget p q hn hG
  have ha := zeroExponent_le_six p
  have horder : totalP 6 p + 2 * totalQ 6 q ≤ 36 := by
    unfold nOf at hn
    unfold totalP totalQ
    omega
  by_cases hK : (Kq 6 q).Nonempty
  · have hQlo : 1 ≤ totalQ 6 q := by
      obtain ⟨k, hk⟩ := hK
      have hkpos := (Finset.mem_filter.mp hk).2
      have hle : q k ≤ totalQ 6 q :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (q j)) (Finset.mem_univ k)
      omega
    have he := unitExponent_le_six_of_nonempty p q hK
    have hQ : totalQ 6 q = 1 := by omega
    have hbeta : unitExponent p q = 5 := by omega
    have halpha : zeroExponent p = 6 := by omega
    exact Or.inr ⟨hQ, hbeta, halpha, by omega, by omega,
      alpha_six_support p halpha⟩
  · have hq := zero_of_totalQ_zero 6 q
      (Paper7Rank.support_sum_zero 6 q (Finset.not_nonempty_iff_eq_empty.mp hK))
    have hQ : totalQ 6 q = 0 := by simp [hq, totalQ]
    have he := qzero_unitExponent_lower p q hq
    have hbeta : unitExponent p q = 6 := by omega
    have halpha : zeroExponent p = 4 := by omega
    have hP : totalP 6 p = 36 := by omega
    have hS : squares 6 p = 576 := by
      have hm' : squares 6 p + 2 * totalQ 6 q + 3 * unitExponent p q = 594 := by
        simpa only [hq, add_zero] using hm
      omega
    have hsupport : (Kp 6 p).card ≤ 4 := by
      have h := support_add_delta0_le_six p
      have hz := halpha
      unfold zeroExponent at hz
      omega
    exact Or.inl ⟨hq, hbeta, halpha, hP, hS, hsupport⟩
#print axioms Paper7C61Higher.root_five_three_two_twos_data

end Paper7C61Higher
