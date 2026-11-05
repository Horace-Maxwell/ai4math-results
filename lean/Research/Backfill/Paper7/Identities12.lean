import Research.Backfill.Paper7.Lemma23
import Research.Backfill.Paper7.SunEdgeCount
import Research.Backfill.Paper7.SunCycleCount
import Research.Backfill.Paper7.IntegralMomentFilters

/-! All four conjuncts of the original identities, for the real frozen SG
and spectrum multisets, preserving eigenvalue multiplicities. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph BackfillPaper7.Challenge
open scoped Classical

namespace Paper7SunMoments

theorem sun_trace_odd_lt_cycle (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (k : ℕ) (hk : Odd k) (hlt : k < b) :
    (((sunGraph b L).adjMatrix ℤ) ^ k).trace = 0 := by
  rw [Paper7Moments.trace_eq_closed_walk_count]
  apply Finset.sum_eq_zero
  intro u _
  let : IsEmpty {w : (sunGraph b L).Walk u u // w.length = k} :=
    ⟨fun w => sun_no_short_odd_closedWalk hb w.val
      (w.property.symm ▸ hk) (by simpa only [w.property] using hlt)⟩
  simp

theorem sg_second_moment (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    ((spec (SG b p q)).map (fun x => x ^ 2)).sum = 2 * (nOf b p q : ℝ) := by
  rw [Paper7Moments.graph_second_moment, sg_edge_card b p q hb]

theorem sg_big_quartic_moment (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) :
    ((bigEigs (SG b p q)).map (fun x => x ^ 2 * (x ^ 2 - 1))).sum =
      2 * ((Theta (SG b p q) : ℤ) : ℝ) + 8 * (if b = 4 then (1 : ℝ) else 0) := by
  have htrace : (((SG b p q).adjMatrix ℤ) ^ 4).trace -
      (((SG b p q).adjMatrix ℤ) ^ 2).trace =
      2 * Theta (SG b p q) + 8 * (cycleCount (SG b p q) 4 : ℤ) := by
    rw [Paper7Moments.trace_four, Paper7Moments.trace_square]
    unfold Theta
    ring
  calc
    _ = ((2 * Theta (SG b p q) + 8 * (cycleCount (SG b p q) 4 : ℤ) : ℤ) : ℝ) := by
      rw [Paper7Moments.integral_big_quartic_eq_traces _ hG, ← Int.cast_sub, htrace]
    _ = _ := by
      rw [sun_cycleCount b (pq b p q) hb 4]
      by_cases hb4 : b = 4 <;> simp [hb4, eq_comm]

theorem sg_big_odd_moment_below (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) (k : ℕ) (hk : Odd k) (hlt : k < b) :
    ((bigEigs (SG b p q)).map (fun x => x ^ k - x)).sum = 0 := by
  rw [Paper7Moments.integral_big_odd_eq_trace _ hG k hk,
    sun_trace_odd_lt_cycle b (pq b p q) hb k hk hlt, Int.cast_zero]

theorem sg_big_odd_moment_at_cycle (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) (hodd : Odd b) :
    ((bigEigs (SG b p q)).map (fun x => x ^ b - x)).sum = 2 * (b : ℝ) := by
  rw [Paper7Moments.integral_big_odd_eq_trace _ hG b hodd,
    Paper7Moments.trace_oddGirth _ (sun_isOddGirth b (pq b p q) hb hodd),
    sun_cycleCount b (pq b p q) hb b]
  simp

theorem check_Identities12 : BackfillPaper7.Challenge.Identities12 := by
  intro b p q hb hG
  refine ⟨sg_second_moment b p q hb, sg_big_quartic_moment b p q hb hG, ?_,
    sg_big_odd_moment_at_cycle b p q hb hG⟩
  intro k hk _hk3 hlt
  exact sg_big_odd_moment_below b p q hb hG k hk hlt

end Paper7SunMoments

#print axioms Paper7SunMoments.sun_trace_odd_lt_cycle
#print axioms Paper7SunMoments.sg_second_moment
#print axioms Paper7SunMoments.sg_big_quartic_moment
#print axioms Paper7SunMoments.sg_big_odd_moment_below
#print axioms Paper7SunMoments.sg_big_odd_moment_at_cycle
#print axioms Paper7SunMoments.check_Identities12

#check (Paper7SunMoments.check_Identities12 : BackfillPaper7.Challenge.Identities12)
