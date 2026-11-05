import Research.Backfill.Paper7.C61IntegerRootProduct
import Research.Backfill.Paper7.C61ProfileShapes

/-! Exact parameter/profile polynomial identities. No classification of the
finite parameter tuples, candidate-table completeness, or CRT converse is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Profile
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Classical

def zeroExponent (p : Fin 6 → ℕ) : ℕ := 6 - (Kp 6 p).card + delta0 6 p
#print axioms Paper7C61Profile.zeroExponent

def unitExponent (p q : Fin 6 → ℕ) : ℕ := 6 - (Kq 6 q).card + deltaE 6 p q 1
#print axioms Paper7C61Profile.unitExponent

theorem zeroExponent_add_totalP (p q : Fin 6 → ℕ) :
    totalP 6 p + zeroExponent p = 6 + mult (SG 6 p q) 0 := by
  have hc : (Kp 6 p).card ≤ 6 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Kp 6 p))
  have hz := (Paper7Lemma22.check_Lemma22 6 p q (by decide)).2.1
  unfold zeroExponent totalP
  omega
#print axioms Paper7C61Profile.zeroExponent_add_totalP

theorem unitExponent_add_totalQ (p q : Fin 6 → ℕ) :
    totalQ 6 q + unitExponent p q = 6 + mult (SG 6 p q) 1 := by
  have hc : (Kq 6 q).card ≤ 6 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Kq 6 q))
  have hu := ((Paper7Lemma22.check_Lemma22 6 p q (by decide)).2.2.1 1 (Or.inl rfl)).1
  unfold unitExponent totalQ
  omega
#print axioms Paper7C61Profile.unitExponent_add_totalQ

theorem zeroExponent_le_six (p : Fin 6 → ℕ) : zeroExponent p ≤ 6 := by
  by_cases hK : Kp 6 p = ∅
  · norm_num [zeroExponent, delta0, hK]
  · have hd := Paper7Rank.delta0_le_card_of_nonempty 6 p
      (Finset.nonempty_iff_ne_empty.mpr hK)
    have hc : (Kp 6 p).card ≤ 6 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ (Kp 6 p))
    unfold zeroExponent
    omega
#print axioms Paper7C61Profile.zeroExponent_le_six

theorem unitExponent_le_six_of_nonempty (p q : Fin 6 → ℕ)
    (hq : (Kq 6 q).Nonempty) : unitExponent p q ≤ 6 := by
  have hd := Paper7Lemma22Gaps.deltaE_nonempty_bound 6 p q 1 hq
  have hc : (Kq 6 q).card ≤ 6 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Kq 6 q))
  unfold unitExponent
  omega
#print axioms Paper7C61Profile.unitExponent_le_six_of_nonempty

theorem unitExponent_le_eight (p q : Fin 6 → ℕ) : unitExponent p q ≤ 8 := by
  by_cases hK : (Kq 6 q).Nonempty
  · have h := unitExponent_le_six_of_nonempty p q hK
    omega
  · have he : Kq 6 q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    have hd := ((Paper7Lemma22.check_Lemma22 6 p q (by decide)).2.2.1 1
      (Or.inl rfl)).2.2 he
    simp only [unitExponent, he, Finset.card_empty, Nat.sub_zero]
    omega
#print axioms Paper7C61Profile.unitExponent_le_eight

theorem clearedF_profile (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) :
    clearedF 6 p q = X ^ zeroExponent p *
      (X ^ 2 - 1) ^ unitExponent p q * polynomial (actual p q) := by
  have ha := zeroExponent_add_totalP p q
  have hu := unitExponent_add_totalQ p q
  have hden : (X ^ totalP 6 p * (X ^ 2 - 1) ^ totalQ 6 q : Polynomial ℤ) ≠ 0 :=
    (Paper7Cleared.monic_denominator_factor (totalP 6 p) (totalQ 6 q)).ne_zero
  apply mul_left_cancel₀ hden
  calc
    _ = X ^ 6 * (X ^ 2 - 1) ^ 6 * graphPhi (SG 6 p q) :=
      Paper7Cleared.cleared_identity 6 p q (by decide)
    _ = X ^ (6 + mult (SG 6 p q) 0) *
        (X ^ 2 - 1) ^ (6 + mult (SG 6 p q) 1) * polynomial (actual p q) := by
      rw [graphPhi_profile p q hn hG, pow_add, pow_add]
      ring
    _ = X ^ (totalP 6 p + zeroExponent p) *
        (X ^ 2 - 1) ^ (totalQ 6 q + unitExponent p q) * polynomial (actual p q) := by
      rw [ha, hu]
    _ = _ := by rw [pow_add, pow_add]; ring
#print axioms Paper7C61Profile.clearedF_profile

theorem exponent_budget (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) :
    zeroExponent p + 2 * unitExponent p q + 2 * card (actual p q) = 24 := by
  have hs := (Paper7Admissible.lemma24_counting_even 6 p q (by decide) hG (by decide)).1
  have hc := Paper7Counting.symmetric_spectrum_card (SG 6 p q) hG hs
  change order 6 (pq 6 p q) = 2 * (Bplus (SG 6 p q)).card +
    mult (SG 6 p q) 1 + mult (SG 6 p q) (-1) + mult (SG 6 p q) 0 at hc
  rw [Paper7Setup.sg_order, ← hs 1, ← actual_card p q hn hG] at hc
  have ha := zeroExponent_add_totalP p q
  have hu := unitExponent_add_totalQ p q
  unfold nOf at hc
  unfold totalP at ha
  unfold totalQ at hu
  omega
#print axioms Paper7C61Profile.exponent_budget

theorem nonempty_q_card_at_least_three (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (hq : (Kq 6 q).Nonempty) :
    3 ≤ card (actual p q) := by
  have h := exponent_budget p q hn hG
  have ha := zeroExponent_le_six p
  have he := unitExponent_le_six_of_nonempty p q hq
  omega
#print axioms Paper7C61Profile.nonempty_q_card_at_least_three

theorem zeroExponent_even (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : Even (zeroExponent p) := by
  have h := exponent_budget p q hn hG
  refine ⟨12 - unitExponent p q - card (actual p q), ?_⟩
  omega
#print axioms Paper7C61Profile.zeroExponent_even

theorem unit_mult_add_square (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) :
    mult (SG 6 p q) 1 + square (actual p q) = nOf 6 p q := by
  have hs := (Paper7Admissible.lemma24_counting_even 6 p q (by decide) hG (by decide)).2.1
  rw [← actual_square p q hn hG] at hs
  have hr : (mult (SG 6 p q) 1 : ℝ) + square (actual p q) = nOf 6 p q := by linarith
  exact_mod_cast hr
#print axioms Paper7C61Profile.unit_mult_add_square

/-- A linear constraint on every surviving parameter row, stronger than the
order bound alone and valid also when either support is empty. -/
theorem parameter_sum_eq_profile (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) :
    square (actual p q) + unitExponent p q = 12 + totalP 6 p + totalQ 6 q := by
  have hs := unit_mult_add_square p q hn hG
  have hu := unitExponent_add_totalQ p q
  unfold nOf at hs
  unfold totalQ at hu
  unfold totalP totalQ
  omega
#print axioms Paper7C61Profile.parameter_sum_eq_profile

/-- Exhaustive finite profile/exponent representation from the original
assumptions. No profile list or parameter exclusion is assumed. -/
theorem finite_profile_representation (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) :
    ∃ (m : Fin 5 → Fin 3) (a : Fin 7) (e : Fin 9),
      Shapes m ∧ a.val + 2 * e.val + 2 * card m = 24 ∧
      Even a.val ∧ square m + e.val = 12 + totalP 6 p + totalQ 6 q ∧
      clearedF 6 p q = X ^ a.val * (X ^ 2 - 1) ^ e.val * polynomial m := by
  have hb := exponent_budget p q hn hG
  have ha := zeroExponent_le_six p
  have he := unitExponent_le_eight p q
  let a : Fin 7 := ⟨zeroExponent p, by omega⟩
  let e : Fin 9 := ⟨unitExponent p q, by omega⟩
  exact ⟨actual p q, a, e, actual_shapes p q hp hn hG, hb,
    zeroExponent_even p q hn hG, parameter_sum_eq_profile p q hn hG,
    clearedF_profile p q hn hG⟩
#print axioms Paper7C61Profile.finite_profile_representation

theorem c61_polynomial : polynomial c61 =
    (X ^ 2 - 4) ^ 2 * (X ^ 2 - 9) ^ 2 * (X ^ 2 - 16) := by
  norm_num [polynomial, c61, value, Fin.prod_univ_succ, mul_assoc]
#print axioms Paper7C61Profile.c61_polynomial

/-- The five-entry branch has no spare order or unit-eigenvalue multiplicity.
Its remaining q total is at most two; q=0 is not silently inferred. -/
theorem saturated_profile_parameters (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (hc : card (actual p q) = 5) :
    actual p q = c61 ∧ nOf 6 p q = 42 ∧ mult (SG 6 p q) 1 = 0 ∧
      totalQ 6 q ≤ 2 ∧ totalP 6 p + 2 * totalQ 6 q = 36 ∧
      zeroExponent p = 2 + 2 * totalQ 6 q ∧ unitExponent p q = 6 - totalQ 6 q ∧
      clearedF 6 p q = X ^ (2 + 2 * totalQ 6 q) *
        (X ^ 2 - 1) ^ (6 - totalQ 6 q) *
        ((X ^ 2 - 4) ^ 2 * (X ^ 2 - 9) ^ 2 * (X ^ 2 - 16)) := by
  have hm := card_five_unique (actual p q) (actual_admissible p q hp hn hG) hc
  have hsq : square (actual p q) = 42 := by rw [hm, c61_square]
  have hnunit := unit_mult_add_square p q hn hG
  have hu := unitExponent_add_totalQ p q
  have hb := exponent_budget p q hn hG
  have horder : nOf 6 p q = 42 := by omega
  have hunit : mult (SG 6 p q) 1 = 0 := by omega
  have hza := zeroExponent_le_six p
  have ha : zeroExponent p = 2 + 2 * totalQ 6 q := by omega
  have hQ : totalQ 6 q ≤ 2 := by omega
  have hPQ : totalP 6 p + 2 * totalQ 6 q = 36 := by
    unfold nOf at horder
    unfold totalP totalQ
    omega
  have he : unitExponent p q = 6 - totalQ 6 q := by omega
  refine ⟨hm, horder, hunit, hQ, hPQ, ha, he, ?_⟩
  rw [clearedF_profile p q hn hG, hm, c61_polynomial, ha, he]
#print axioms Paper7C61Profile.saturated_profile_parameters

/-- Each even gap contains the successor of its starting support vertex.
Distinct starts have distinct successors, all outside the support. -/
theorem evenGaps_le_complement (b : ℕ) (K : Finset (Fin b)) :
    evenGaps b K ≤ b - K.card := by
  let E := K.filter (fun k => ∃ d ∈ Finset.Icc 1 b, Even d ∧
    ((finRotate b) ^ d) k ∈ K ∧
      ∀ d' ∈ Finset.Ico 1 d, ((finRotate b) ^ d') k ∉ K)
  have hsub : E.image (finRotate b) ⊆ Kᶜ := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨d, hd, he, _hend, hclear⟩ := (Finset.mem_filter.mp hk).2
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd2 : 2 ≤ d := by
      obtain ⟨t, ht⟩ := he
      omega
    apply Finset.mem_compl.mpr
    have h := hclear 1 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
    simpa only [pow_one] using h
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (finRotate b).injective, Finset.card_compl,
    Fintype.card_fin] at hcard
  exact hcard
#print axioms Paper7C61Profile.evenGaps_le_complement

theorem support_add_delta0_le_six (p : Fin 6 → ℕ) :
    (Kp 6 p).card + delta0 6 p ≤ 6 := by
  by_cases hK : Kp 6 p = ∅
  · norm_num [delta0, hK]
  · have h := evenGaps_le_complement 6 (Kp 6 p)
    have hc : (Kp 6 p).card ≤ 6 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ (Kp 6 p))
    rw [delta0, ite_eq_right hK]
    omega
#print axioms Paper7C61Profile.support_add_delta0_le_six

theorem saturated_support_bound (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (hc : card (actual p q) = 5) :
    (Kp 6 p).card + totalQ 6 q ≤ 5 := by
  obtain ⟨_hm, _hn, _hu, _hQ, _hPQ, ha, _he, _hpoly⟩ :=
    saturated_profile_parameters p q hp hn hG hc
  have hsupport := support_add_delta0_le_six p
  unfold zeroExponent at ha
  omega
#print axioms Paper7C61Profile.saturated_support_bound

end Paper7C61Profile
