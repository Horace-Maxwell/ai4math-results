import Research.Backfill.Paper7.AdmissibleSpectrum
import Research.Backfill.Paper7.CycleFeatureCounts
import Research.Backfill.Paper7.CycleInterlacing
import Research.Backfill.Paper7.Lemma53

/-! Source-only candidate for cycle-filter admissibility and the exact window.
The d=b branch is proved from equality of the complete assigned sum, rather
than replacing the frozen zero-remainder window with the broader Lemma53 bound. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningSpectrum
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem actualCounts_posCard (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    posCard (actualCounts b x hb) = Ngt (SG b x.1 x.2) 1 := by
  simpa only [posCard, actualCounts_pos] using
    (positive_threshold (SG b x.1 x.2) hG (budget_spectral_window b N x hb hN hx)).symm
#print axioms Paper7PruningSpectrum.actualCounts_posCard

theorem actualCounts_negCard (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) (ho : Odd b) :
    negCard (actualCounts b x hb) = Nlt (SG b x.1 x.2) (-1) := by
  simpa only [negCard, actualCounts_neg_odd b x hb ho] using
    (negative_threshold (SG b x.1 x.2) hG (budget_spectral_window b N x hb hN hx)).symm
#print axioms Paper7PruningSpectrum.actualCounts_negCard

theorem actualCounts_admissible (cyc : Bool) (b N : ℕ) (x : PQ b)
    (hb : 3 ≤ b) (hN : N ≤ 49) (hx : Budget b N x)
    (hG : IsIntegralGraph (SG b x.1 x.2)) : Admissible cyc b N (actualCounts b x hb) := by
  refine ⟨actualCounts_admissibleBase b N x hb hN hx hG, ?_⟩
  intro _hcyc
  have hcycle := Paper7Lemma41.lemma41_interlacing b x.1 x.2 hb
  constructor
  · rw [cyclicPositive_eq_Ngt b hb, actualCounts_posCard b N x hb hN hx hG]
    exact hcycle.1
  · intro ho
    rw [cyclicNegative_eq_Nlt b hb, actualCounts_negCard b N x hb hN hx hG ho]
    exact hcycle.2
#print axioms Paper7PruningSpectrum.actualCounts_admissible

theorem prefix_weight_cast (b d : ℕ) (x : PQ b) :
    (weight («prefix» d x) : ℤ) =
      ∑ k ∈ univ.filter (fun k : Fin b => k.val < d), ((x.1 k : ℤ) + 2 * x.2 k) := by
  classical
  simp only [weight, pSum, qSum, «prefix», Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [mul_sum, ← sum_add_distrib, Finset.sum_filter]
  apply sum_congr rfl
  intro k _
  by_cases hk : k.val < d <;> simp [hk]
#print axioms Paper7PruningSpectrum.prefix_weight_cast

theorem prefixTheta_full (b : ℕ) (x : PQ b) : prefixTheta b x = theta x := by
  have h : (univ.filter (fun i : Fin b => i.val < b)) = univ :=
    filter_eq_self.mpr (fun i _ => i.isLt)
  simp only [prefixTheta, h, theta]
#print axioms Paper7PruningSpectrum.prefixTheta_full

theorem actual_theta_in_window (b N d : ℕ) (x : PQ b) (hd : d ≤ b)
    (hx : Budget b N x) :
    windowLo d x ≤ theta x ∧ theta x ≤ windowHi N d x := by
  have hn : nOf b x.1 x.2 ≤ N := by rw [nOf_eq_b_weight]; exact hx.2
  have h := check_Lemma53 b d N x.1 x.2 hd hn
  change prefixTheta d x + 2 * ((b : ℤ)-d) ≤ theta x ∧
    theta x ≤ prefixTheta d x +
      gW ((N : ℤ)-b-(∑ k ∈ univ.filter (fun k : Fin b => k.val < d),
        ((x.1 k : ℤ) + 2*x.2 k))) + 2 * ((b : ℤ)-d-1) at h
  refine ⟨h.1, ?_⟩
  by_cases hdb : d < b
  · have hupper := h.2
    rw [← prefix_weight_cast b d x] at hupper
    simpa only [windowHi, ite_eq_left hdb, gW, add_assoc] using hupper
  · have hEq : d = b := by omega
    subst d
    simp only [windowHi, lt_self_iff_false, ite_false, add_zero, prefixTheta_full, le_refl]
#print axioms Paper7PruningSpectrum.actual_theta_in_window

theorem actual_windowPass (cyc : Bool) (b N d : ℕ) (x : PQ b) (hb : 3 ≤ b)
    (hd : d ≤ b) (hN : N ≤ 49) (hx : Budget b N x)
    (hG : IsIntegralGraph (SG b x.1 x.2)) : WindowPass cyc b N d x := by
  refine ⟨actualCounts b x hb, actualCounts_admissible cyc b N x hb hN hx hG, ?_⟩
  rw [actualCounts_targetTheta b N x hb hN hx hG]
  exact actual_theta_in_window b N d x hd hx
#print axioms Paper7PruningSpectrum.actual_windowPass

/-- Exactly original pruning conjunct 5, including d=0 and d=b. -/
theorem pruning_windowPass :
    ∀ b N d : ℕ, 3 ≤ b → d ≤ b → N ≤ 49 → ∀ x, Budget b N x →
      IsIntegralGraph (SG b x.1 x.2) → WindowPass true b N d x := by
  intro b N d hb hd hN x hx hG
  exact actual_windowPass true b N d x hb hd hN hx hG
#print axioms Paper7PruningSpectrum.pruning_windowPass

end Paper7PruningSpectrum
