import Research.Backfill.Paper7.MomentB6TopMomentShape

/-! Uncompiled original-PQ reconstruction of the top catalogue fibre.
All six positions remain ordered.  The actual original acceptance predicate
is checked for every reconstructed row, with catalogue witness (40,1272). -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b6TopMomentRow (i : Fin 6) : PQ 6 :=
  (fun k => if k = i then 33 else 0, fun k => if k = i then 1 else 0)
#print axioms Paper7MomentCounts.b6TopMomentRow

theorem b6TopMomentRow_features (i : Fin 6) :
    weight (b6TopMomentRow i) = 35 ∧ qSum (b6TopMomentRow i) = 1 ∧
      theta (b6TopMomentRow i) = 1272 := by
  have hp : pSum (b6TopMomentRow i) = 33 := by simp [pSum, b6TopMomentRow]
  have hq : qSum (b6TopMomentRow i) = 1 := by simp [qSum, b6TopMomentRow]
  have ht : theta (b6TopMomentRow i) =
      ∑ k : Fin 6, (2 + if k = i then 1260 else 0 : ℤ) := by
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hki : k = i <;> norm_num [b6TopMomentRow, thetaV, hki]
  refine ⟨by simp [weight, hp, hq], hq, ?_⟩
  rw [ht]
  norm_num [Finset.sum_add_distrib]
#print axioms Paper7MomentCounts.b6TopMomentRow_features

theorem b6TopMomentRow_guard (i : Fin 6) : b6CandidateGuard (b6TopMomentRow i) := by
  obtain ⟨hw, hq, ht⟩ := b6TopMomentRow_features i
  unfold b6CandidateGuard
  rw [hw, hq, ht]
  refine ⟨by norm_num, by norm_num, (40,1272), ?_, by rfl, by norm_num, by norm_num⟩
  simp [b6FeatureCatalog]
#print axioms Paper7MomentCounts.b6TopMomentRow_guard

/-- Completeness uses only the original budget and theta; no catalogue coverage
or list of rows is assumed. -/
theorem b6_budget_top_moment_row (x : PQ 6) (hx : Budget 6 42 x)
    (htheta : theta x = 1272) : ∃ i : Fin 6, x = b6TopMomentRow i := by
  let v := pqToZQ x
  have hback : zqToPQ v = x := (pqEquivZQ 6).left_inv x
  have hv : Budget 6 42 (zqToPQ v) := by rw [hback]; exact hx
  have hb := (zq_budget_iff 6 42 v).mp hv
  have hb36 : (∑ k, v.val.1 k) + (∑ k, v.val.2 k) ≤ 36 := by omega
  have ht := b6_zq_theta v
  rw [hback, htheta] at ht
  obtain ⟨hQ, i, hi, hrest⟩ := b6_top_moment_shape v.val.1 (∑ k, v.val.2 k) hb36 ht.symm
  have hzero (k : Fin 6) (hki : k ≠ i) : x.1 k = 0 ∧ x.2 k = 0 := by
    have h := hrest k hki
    change x.1 k + x.2 k = 0 at h
    omega
  have hqi : x.2 i = 1 := by
    have he : (∑ k, v.val.2 k) = x.2 i := by
      apply Finset.sum_eq_single i
      · intro k _hk hki
        exact (hzero k hki).2
      · intro hnot
        exact (hnot (Finset.mem_univ i)).elim
    omega
  have hpi : x.1 i = 33 := by
    change x.1 i + x.2 i = 34 at hi
    omega
  refine ⟨i, ?_⟩
  apply Prod.ext
  · funext k
    by_cases hki : k = i
    · subst k
      simpa only [b6TopMomentRow, ite_true] using hpi
    · simpa only [b6TopMomentRow, ite_eq_right hki] using (hzero k hki).1
  · funext k
    by_cases hki : k = i
    · subst k
      simpa only [b6TopMomentRow, ite_true] using hqi
    · simpa only [b6TopMomentRow, ite_eq_right hki] using (hzero k hki).2
#print axioms Paper7MomentCounts.b6_budget_top_moment_row

theorem b6_top_moment_guard_iff (x : PQ 6) :
    b6CandidateGuard x ∧ theta x = 1272 ↔ ∃ i : Fin 6, x = b6TopMomentRow i := by
  constructor
  · rintro ⟨hg, ht⟩
    have hb : Budget 6 42 x := ⟨hg.1, by have hw := hg.2.1; omega⟩
    exact b6_budget_top_moment_row x hb ht
  · rintro ⟨i, rfl⟩
    exact ⟨b6TopMomentRow_guard i, (b6TopMomentRow_features i).2.2⟩
#print axioms Paper7MomentCounts.b6_top_moment_guard_iff

theorem b6TopMomentRow_injective : Function.Injective b6TopMomentRow := by
  intro i j hij
  by_contra hne
  have h := congrArg (fun x : PQ 6 => x.2 i) hij
  simp [b6TopMomentRow, hne] at h
#print axioms Paper7MomentCounts.b6TopMomentRow_injective

end Paper7MomentCounts
