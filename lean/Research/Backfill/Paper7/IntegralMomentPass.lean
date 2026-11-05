import Research.Backfill.Paper7.SpectralWindowPass
import Research.Backfill.Paper7.Lemma42

/-! Source-only: every moment/load/count flag uses the same actual multiplicity
tuple. No accepted-search or nonempty-candidate premise is introduced. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningGuards
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7PruningSpectrum

theorem actual_posCard_eq_Bplus (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    posCard (actualCounts b x hb) = (Bplus (SG b x.1 x.2)).card := by
  simpa only [posCard, actualCounts_pos] using
    (positive_card (SG b x.1 x.2) hG (budget_spectral_window b N x hb hN hx)).symm
#print axioms Paper7PruningGuards.actual_posCard_eq_Bplus

theorem actual_s2_le_order (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    s2 b (actualCounts b x hb) ≤
      if Even b then (b + weight x : ℤ) else 2 * (b + weight x) := by
  have h := actualCounts_s2_budget b (b + weight x) x hb (hx.2.trans hN)
    ⟨hx.1, le_rfl⟩ hG
  simpa only [Nat.cast_add] using h
#print axioms Paper7PruningGuards.actual_s2_le_order

theorem actual_load_bound (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    (if Even b then (b + weight x : ℤ) - max (qSum x) 2
     else 2 * (b + weight x : ℤ) - 2 * max (qSum x) 2) ≤
      s2 b (actualCounts b x hb) := by
  have hu := Paper7Admissible.lemma24_unit_multiplicity_bounds b x.1 x.2 hb
  have hp : (mult (SG b x.1 x.2) 1 : ℝ) ≤ (max (qSum x) 2 : ℕ) := by
    exact_mod_cast hu.1
  have hn : (mult (SG b x.1 x.2) (-1) : ℝ) ≤ (max (qSum x) 2 : ℕ) := by
    exact_mod_cast hu.2
  by_cases he : Even b
  · rw [ite_eq_left he]
    have h := (Paper7Admissible.lemma24_counting_even b x.1 x.2 hb hG he).2.1
    rw [← encoded_s2_even b N x hb hN hx hG he, nOf_eq_b_weight] at h
    have hr : ((b : ℝ) + weight x) - (max (qSum x) 2 : ℕ) ≤
        (s2 b (actualCounts b x hb) : ℝ) := by
      push_cast at h
      linarith
    exact_mod_cast hr
  · rw [ite_eq_right he]
    have ho := Nat.not_even_iff_odd.mp he
    have h := Paper7Admissible.graph_square_partition (SG b x.1 x.2) hG
    rw [Paper7SunMoments.sg_second_moment b x.1 x.2 hb,
      ← encoded_s2_odd b N x hb hN hx hG ho, nOf_eq_b_weight] at h
    have hr : 2 * ((b : ℝ) + weight x) - 2 * (max (qSum x) 2 : ℕ) ≤
        (s2 b (actualCounts b x hb) : ℝ) := by
      push_cast at h
      linarith
    exact_mod_cast hr
#print axioms Paper7PruningGuards.actual_load_bound

theorem actual_even_count_bounds (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) (he : Even b) :
    0 ≤ 2 * s2 b (actualCounts b x hb) - (b + weight x) -
        2 * posCard (actualCounts b x hb) ∧
    2 * s2 b (actualCounts b x hb) - (b + weight x) -
        2 * posCard (actualCounts b x hb) ≤ max (pSum x) 2 := by
  have hzero := (Paper7Counting.lemma42_multiplicities b x.1 x.2 hb he hG).2.2
  rw [← encoded_s2_even b N x hb hN hx hG he,
    ← actual_posCard_eq_Bplus b N x hb hN hx hG, nOf_eq_b_weight] at hzero
  have hz : (mult (SG b x.1 x.2) 0 : ℤ) =
      2 * s2 b (actualCounts b x hb) - (b + weight x) -
        2 * posCard (actualCounts b x hb) := by exact_mod_cast hzero
  have hnonneg : (0 : ℤ) ≤ mult (SG b x.1 x.2) 0 := by positivity
  have hmax : (mult (SG b x.1 x.2) 0 : ℤ) ≤ (max (pSum x) 2 : ℕ) := by
    exact_mod_cast (Paper7Lemma22.check_Lemma22 b x.1 x.2 hb).2.2.2.1
  omega
#print axioms Paper7PruningGuards.actual_even_count_bounds

theorem actual_even_order_bound (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) (he : Even b) :
    (b + weight x : ℤ) ≤ 2 * s2 b (actualCounts b x hb) -
      2 * posCard (actualCounts b x hb) := by
  have h := (actual_even_count_bounds b N x hb hN hx hG he).1
  omega
#print axioms Paper7PruningGuards.actual_even_order_bound

theorem momentPass_integral (cyc load cnt : Bool) (b N : ℕ) (x : PQ b)
    (hb : 3 ≤ b) (hN : N ≤ 49) (hx : Budget b N x)
    (hG : IsIntegralGraph (SG b x.1 x.2)) : MomentPass cyc load cnt b N x := by
  exact ⟨actualCounts b x hb, actualCounts_admissible cyc b N x hb hN hx hG,
    actualCounts_m4 b N x hb hN hx hG, actual_s2_le_order b N x hb hN hx hG,
    fun _ => actual_load_bound b N x hb hN hx hG,
    fun _ he => actual_even_count_bounds b N x hb hN hx hG he⟩
#print axioms Paper7PruningGuards.momentPass_integral

end Paper7PruningGuards
