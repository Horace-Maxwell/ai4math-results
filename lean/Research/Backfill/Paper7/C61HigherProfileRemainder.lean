import Research.Backfill.Paper7.C61PerronFiveExclusions
import Research.Backfill.Paper7.C61RootFourThreeExclusion

/-! Recovery continuation. Every statement below is source-only and uncompiled.
The profile alternatives are necessary conditions on arbitrary original p,q;
they do not assert that a profile or its moments suffice for integrality. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Higher
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small
open scoped BigOperators Classical

theorem cap22_sum24_square528_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 24) (hS : squares 6 p = 528)
    (hc : ∀ k, p k ≤ 22) : False := by
  obtain ⟨M, _h0, hhi, hm, hs⟩ := capped_maximum_moment p 24 528 22 hP hS hc
  have heq : M = 22 := by omega
  rw [heq] at hs
  norm_num at hs
#print axioms Paper7C61Higher.cap22_sum24_square528_impossible

theorem cap22_sum25_square525_impossible (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 25) (hS : squares 6 p = 525)
    (hc : ∀ k, p k ≤ 22) : False := by
  obtain ⟨M, _h0, hhi, hm, hs⟩ := capped_maximum_moment p 25 525 22 hP hS hc
  norm_num at hhi hm hs
  have hlo : 21 ≤ M := by omega
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith
#print axioms Paper7C61Higher.cap22_sum25_square525_impossible

/-- This closes the fourth and last profile in the card-at-most-two
Perron-five branch, without assuming a parameter table. -/
theorem root_five_one_two_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 1)
    (h1 : (actual p q 1).val = 0) (h2 : (actual p q 2).val = 0) : False := by
  have hload := no_six_load_le_twenty_two p q hn hG h5.2
  have hcap : ∀ k, p k ≤ 22 := by intro k; have := hload k; omega
  obtain ⟨hc, hs, hf⟩ := root_five_profile (actual p q) h5
  rw [h0, h1, h2] at hc hs hf
  have hq := q_zero_of_card_le_two p q hn hG (by omega)
  have hQ : totalQ 6 q = 0 := by simp [hq, totalQ]
  have he := unitExponent_le_eight p q
  have ha := zeroExponent_le_six p
  have hb := exponent_budget p q hn hG
  have hsum := parameter_sum_eq_profile p q hn hG
  have hm := q_zero_moment p q hn hG hq
  rw [hf] at hm
  have hcases : unitExponent p q = 7 ∨ unitExponent p q = 8 := by omega
  rcases hcases with he7 | he8
  · have hP : totalP 6 p = 24 := by omega
    have hS : squares 6 p = 528 := by
      rw [hP] at hm
      norm_num at hm
      exact_mod_cast (by linarith : (squares 6 p : ℤ) = 528)
    exact cap22_sum24_square528_impossible p hP hS hcap
  · have hP : totalP 6 p = 25 := by omega
    have hS : squares 6 p = 525 := by
      rw [hP] at hm
      norm_num at hm
      exact_mod_cast (by linarith : (squares 6 p : ℤ) = 525)
    exact cap22_sum25_square525_impossible p hP hS hcap
#print axioms Paper7C61Higher.root_five_one_two_impossible

theorem root_five_card_at_least_three (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) : 3 ≤ card (actual p q) := by
  by_contra h
  obtain ⟨h0, h1, h2⟩ := root_five_small_card_profile p q hn hG h5 (by omega)
  exact root_five_one_two_impossible p q hn hG h5 h0 h1 h2
#print axioms Paper7C61Higher.root_five_card_at_least_three

/-- Exhaustive necessary Perron-four profiles after the small-card
exclusions. The last alternative is the separate saturated branch. -/
theorem root_four_remaining_shapes (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) :
    ((actual p q 0).val = 2 ∧ (actual p q 1).val = 0) ∨
    ((actual p q 0).val = 1 ∧ (actual p q 1).val = 1) ∨
    ((actual p q 0).val = 2 ∧ (actual p q 1).val = 1) ∨
    ((actual p q 0).val = 0 ∧ (actual p q 1).val = 2) ∨
    ((actual p q 0).val = 1 ∧ (actual p q 1).val = 2) ∨
    ((actual p q 0).val = 2 ∧ (actual p q 1).val = 2) := by
  have hc := root_four_card_at_least_three p q hn hG h4
  have hcard := (root_four_profile (actual p q) h4).1
  have h0 := (actual p q 0).isLt
  have h1 := (actual p q 1).isLt
  omega
#print axioms Paper7C61Higher.root_four_remaining_shapes

/-- This uses actual_shapes, which is derived from the original assumptions;
it does not replace arbitrary p,q by a list of sample rotations. -/
theorem root_five_remaining_shapes (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (h5 : RootFive (actual p q)) :
    (actual p q 2).val = 0 ∧
      (((actual p q 0).val = 2 ∧ (actual p q 1).val = 0) ∨
        ((actual p q 0).val = 1 ∧ (actual p q 1).val = 1) ∨
        ((actual p q 0).val = 2 ∧ (actual p q 1).val = 1)) := by
  have hc := root_five_card_at_least_three p q hn hG h5
  have hcard := (root_five_profile (actual p q) h5).1
  have h0 := (actual p q 0).isLt
  have hshape := actual_shapes p q hp hn hG
  rcases hshape with ⟨_h1, _h2, h3, _h4⟩ | ⟨_h2, h3, _h4⟩ |
    ⟨_h3, _h4, hh⟩ | ⟨h4, _h3, _h2, _h1, _h0⟩
  · have := h5.1
    omega
  · have := h5.1
    omega
  · rcases hh with ⟨h2, h1⟩ | ⟨h2, h1, h0⟩
    · exact ⟨h2, by omega⟩
    · omega
  · have := h5.2
    omega
#print axioms Paper7C61Higher.root_five_remaining_shapes

/-- For every three-entry actual profile with a nonempty q support, both
exceptional exponents are forced. The fourth moment remains an exact
constraint on the actual parameters. -/
theorem card_three_qpositive_data (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (hc : card (actual p q) = 3) (hK : (Kq 6 q).Nonempty) :
    unitExponent p q = 6 ∧ zeroExponent p = 6 ∧
      totalP 6 p + totalQ 6 q + 6 = square (actual p q) ∧
      1 ≤ totalQ 6 q ∧ totalP 6 p + 2 * totalQ 6 q ≤ 36 ∧
      (Kp 6 p).card ≤ 3 ∧ (Kq 6 q).card ≤ 3 := by
  have he := unitExponent_le_six_of_nonempty p q hK
  have ha := zeroExponent_le_six p
  have hb := exponent_budget p q hn hG
  have hbeta : unitExponent p q = 6 := by omega
  have halpha : zeroExponent p = 6 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hQ : 1 ≤ totalQ 6 q := by
    obtain ⟨k, hk⟩ := hK
    have hkpos := (Finset.mem_filter.mp hk).2
    have hle : q k ≤ totalQ 6 q :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (q j)) (Finset.mem_univ k)
    omega
  have horder : totalP 6 p + 2 * totalQ 6 q ≤ 36 := by
    unfold nOf at hn
    unfold totalP totalQ
    omega
  have hqc := q_support_le_profile p q hn hG
  exact ⟨hbeta, halpha, by omega, hQ, horder,
    alpha_six_support p halpha, by omega⟩
#print axioms Paper7C61Higher.card_three_qpositive_data

end Paper7C61Higher
