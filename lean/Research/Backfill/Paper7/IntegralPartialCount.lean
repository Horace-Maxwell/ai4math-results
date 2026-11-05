import Research.Backfill.Paper7.IntegralMomentPass
import Research.Backfill.Paper7.PartialAssignmentCounting

/-! Source-only: actual partial sums and the original integer min/max guard.
No premise on a completed total is substituted for the partial P threshold. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningGuards
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7PruningSpectrum

theorem pSum_prefix_filter (b d : ℕ) (x : PQ b) :
    pSum («prefix» d x) = ∑ k ∈ univ.filter (fun k : Fin b => k.val < d), x.1 k := by
  simp only [pSum, «prefix», Finset.sum_filter]
#print axioms Paper7PruningGuards.pSum_prefix_filter

theorem qSum_prefix_filter (b d : ℕ) (x : PQ b) :
    qSum («prefix» d x) = ∑ k ∈ univ.filter (fun k : Fin b => k.val < d), x.2 k := by
  simp only [qSum, «prefix», Finset.sum_filter]
#print axioms Paper7PruningGuards.qSum_prefix_filter

theorem prefix_sums_le_full (b d : ℕ) (x : PQ b) :
    pSum («prefix» d x) ≤ pSum x ∧ qSum («prefix» d x) ≤ qSum x ∧
      weight («prefix» d x) ≤ weight x := by
  have hp : pSum («prefix» d x) ≤ pSum x := by
    rw [pSum_prefix_filter]
    exact Paper7PartialCounting.partial_sum_le_total b _ x.1
  have hq : qSum («prefix» d x) ≤ qSum x := by
    rw [qSum_prefix_filter]
    exact Paper7PartialCounting.partial_sum_le_total b _ x.2
  refine ⟨hp, hq, ?_⟩
  unfold weight
  omega
#print axioms Paper7PruningGuards.prefix_sums_le_full

theorem partialCountPass_integral (b N d : ℕ) (x : PQ b) (hb : 3 ≤ b)
    (hN : N ≤ 49) (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2))
    (he : Even b) : PartialCountPass b N d x (actualCounts b x hb) := by
  have hsum := prefix_sums_le_full b d x
  have horder := actual_even_order_bound b N x hb hN hx hG he
  have hs2 := actual_s2_le_order b N x hb hN hx hG
  rw [ite_eq_left he] at hs2
  have hbudget : (b + weight x : ℤ) ≤ N := by exact_mod_cast hx.2
  have hpartial : (b + weight («prefix» d x) : ℤ) ≤ b + weight x := by
    exact_mod_cast Nat.add_le_add_left hsum.2.2 b
  dsimp only [PartialCountPass]
  constructor
  · exact (max_le hpartial hs2).trans (le_min hbudget horder)
  · intro hP
    have hn : nOf b x.1 x.2 ≤ N := by rw [nOf_eq_b_weight]; exact hx.2
    have h := Paper7PartialCounting.partial_counting_on_subset b N x.1 x.2 hb he hG hn
      (univ.filter (fun k : Fin b => k.val < d))
      (by simpa only [pSum_prefix_filter] using hP)
    rw [← encoded_s2_even b N x hb hN hx hG he,
      ← actual_posCard_eq_Bplus b N x hb hN hx hG,
      ← qSum_prefix_filter b d x] at h
    exact_mod_cast h
#print axioms Paper7PruningGuards.partialCountPass_integral

theorem prefix_load_bound (b N d : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    (if Even b then (b : ℤ) + pSum («prefix» d x) + qSum («prefix» d x) - 2
     else 2*((b : ℤ) + pSum («prefix» d x) + qSum («prefix» d x) - 2)) ≤
      s2 b (actualCounts b x hb) := by
  have h := actual_load_bound b N x hb hN hx hG
  have hm := prefix_sums_le_full b d x
  have hp : (pSum («prefix» d x) : ℤ) ≤ pSum x := by exact_mod_cast hm.1
  have hq : (qSum («prefix» d x) : ℤ) ≤ qSum x := by exact_mod_cast hm.2.1
  have hmax : (max (qSum x) 2 : ℕ) ≤ qSum x + 2 := by omega
  have hmaxZ : ((max (qSum x) 2 : ℕ) : ℤ) ≤ qSum x + 2 := by exact_mod_cast hmax
  simp only [weight, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
  by_cases he : Even b
  · simp only [ite_eq_left he] at h ⊢
    omega
  · simp only [ite_eq_right he] at h ⊢
    omega
#print axioms Paper7PruningGuards.prefix_load_bound

end Paper7PruningGuards
