import Research.Backfill.Paper7.IntegralPartialCount
import Research.Backfill.Paper7.PrefixInertiaBounds
import Research.Backfill.Paper7.LegacyEnumeration

/-! Source-only A/B prefix soundness on the actual integral completion.
WindowPass is used as a separate bound, never as a monotone break predicate. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningGuards
open Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7PruningSpectrum

theorem aMonotonePass_integral (cyc cnt : Bool) (b N d : ℕ) (x : PQ b)
    (hb : 3 ≤ b) (hd : d < b) (hN : N ≤ 49) (hx : Budget b N x)
    (hG : IsIntegralGraph (SG b x.1 x.2)) : AMonotonePass cyc cnt b N d x := by
  refine ⟨actualCounts b x hb, actualCounts_admissible cyc b N x hb hN hx hG,
    ?_, prefix_load_bound b N d x hb hN hx hG,
    prefix_feature_bounds b N d x hb hd hN hx hG, ?_⟩
  · have hw := (actual_theta_in_window b N d x hd.le hx).1
    rw [actualCounts_m4 b N x hb hN hx hG]
    by_cases he : Even b
    · simp only [ite_eq_left he]
      have hcorrection : (0 : ℤ) ≤ if b = 4 then 4 else 0 := by split <;> norm_num
      omega
    · simp only [ite_eq_right he]
      omega
  · intro _hcnt he
    exact partialCountPass_integral b N d x hb hN hx hG he
#print axioms Paper7PruningGuards.aMonotonePass_integral

theorem aReaches_integral (cyc cnt : Bool) (b N : ℕ) (x : PQ b)
    (hb : 3 ≤ b) (hN : N ≤ 49) (hx : Budget b N x)
    (hG : IsIntegralGraph (SG b x.1 x.2)) (hrot : RotationRule key1000 b x) :
    AReaches cyc cnt b N x := by
  refine ⟨hx, hrot, momentPass_integral cyc true false b N x hb hN hx hG, ?_⟩
  intro d _hd1 hdb
  exact ⟨aMonotonePass_integral cyc cnt b N d x hb hdb hN hx hG,
    actual_windowPass cyc b N d x hb hdb.le hN hx hG⟩
#print axioms Paper7PruningGuards.aReaches_integral

theorem bReaches_integral (cyc cnt useWindow rotation : Bool) (b N : ℕ) (x : PQ b)
    (hb : 3 ≤ b) (hN : N ≤ 49) (hx : Budget b N x)
    (hG : IsIntegralGraph (SG b x.1 x.2))
    (hrot : rotation = true → RotationRule key1000 b x) :
    BReaches cyc cnt useWindow rotation b N x := by
  refine ⟨hx, momentPass_integral cyc true cnt b N x hb hN hx hG, hrot, ?_⟩
  intro _hwindow d _hd1 hdb
  refine ⟨actualCounts b x hb, actualCounts_admissible cyc b N x hb hN hx hG,
    ?_, ?_, ?_⟩
  · rw [actualCounts_targetTheta b N x hb hN hx hG]
    exact (actual_theta_in_window b N d x hdb hx).1
  · rw [actualCounts_targetTheta b N x hb hN hx hG]
    exact (actual_theta_in_window b N d x hdb hx).2
  · intro _hcnt he
    exact partialCountPass_integral b N d x hb hN hx hG he
#print axioms Paper7PruningGuards.bReaches_integral

theorem dStage_integral (load cyc canonical rotation noPruning : Bool)
    (b N : ℕ) (x : PQ b) (hb : 3 ≤ b) (hN : N ≤ 49)
    (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2))
    (hcan : canonical = true → Canonical (if rotation then keyWeight else key64) rotation b x)
    (hrot : rotation = true → RotationRule (fun p q => p+2*q) b x) :
    DStage load cyc canonical rotation noPruning b N x := by
  exact ⟨hx, fun _ => momentPass_integral cyc load false b N x hb hN hx hG, hcan, hrot⟩
#print axioms Paper7PruningGuards.dStage_integral

end Paper7PruningGuards
