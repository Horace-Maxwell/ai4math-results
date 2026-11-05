import Research.Backfill.Paper7.LegacyEnumeration

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
Exact correctness of the frozen D1/D2 recurrences, including length zero.
No Lean execution or mathematical acceptance is claimed for this source.
-/
set_option autoImplicit false
noncomputable section

namespace Paper7Pruning
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

def pqCons {r : ℕ} (p q : ℕ) (x : PQ r) : PQ (r + 1) :=
  (Fin.cons p x.1, Fin.cons q x.2)
#print axioms Paper7Pruning.pqCons

def pqTail {r : ℕ} (x : PQ (r + 1)) : PQ r :=
  (Fin.tail x.1, Fin.tail x.2)
#print axioms Paper7Pruning.pqTail

theorem pqCons_head_tail {r : ℕ} (x : PQ (r + 1)) :
    pqCons (x.1 0) (x.2 0) (pqTail x) = x := by
  apply Prod.ext
  · exact Fin.cons_self_tail x.1
  · exact Fin.cons_self_tail x.2
#print axioms Paper7Pruning.pqCons_head_tail

theorem pSum_pqCons {r : ℕ} (p q : ℕ) (x : PQ r) :
    pSum (pqCons p q x) = p + pSum x := by
  simp only [pSum, pqCons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
#print axioms Paper7Pruning.pSum_pqCons

theorem qSum_pqCons {r : ℕ} (p q : ℕ) (x : PQ r) :
    qSum (pqCons p q x) = q + qSum x := by
  simp only [qSum, pqCons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
#print axioms Paper7Pruning.qSum_pqCons

theorem weight_pqCons {r : ℕ} (p q : ℕ) (x : PQ r) :
    weight (pqCons p q x) = p + 2 * q + weight x := by
  simp only [weight, pSum_pqCons, qSum_pqCons]
  omega
#print axioms Paper7Pruning.weight_pqCons

theorem theta_pqCons {r : ℕ} (p q : ℕ) (x : PQ r) :
    theta (pqCons p q x) = thetaV p q + theta x := by
  simp only [theta, pqCons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
#print axioms Paper7Pruning.theta_pqCons

theorem weight_head_tail {r : ℕ} (x : PQ (r + 1)) :
    weight x = x.1 0 + 2 * x.2 0 + weight (pqTail x) := by
  simpa only [pqCons_head_tail] using
    weight_pqCons (x.1 0) (x.2 0) (pqTail x)
#print axioms Paper7Pruning.weight_head_tail

theorem qSum_head_tail {r : ℕ} (x : PQ (r + 1)) :
    qSum x = x.2 0 + qSum (pqTail x) := by
  simpa only [pqCons_head_tail] using
    qSum_pqCons (x.1 0) (x.2 0) (pqTail x)
#print axioms Paper7Pruning.qSum_head_tail

theorem theta_head_tail {r : ℕ} (x : PQ (r + 1)) :
    theta x = thetaV (x.1 0) (x.2 0) + theta (pqTail x) := by
  simpa only [pqCons_head_tail] using
    theta_pqCons (x.1 0) (x.2 0) (pqTail x)
#print axioms Paper7Pruning.theta_head_tail

theorem thetaV_nonneg (p q : ℕ) : 0 ≤ thetaV p q := by
  unfold thetaV
  positivity
#print axioms Paper7Pruning.thetaV_nonneg

theorem theta_nonneg {r : ℕ} (x : PQ r) : 0 ≤ theta x := by
  unfold theta
  exact Finset.sum_nonneg (fun i _ => thetaV_nonneg (x.1 i) (x.2 i))
#print axioms Paper7Pruning.theta_nonneg

/-- The literal D1 recursion enumerates exactly the prescribed weight and theta. -/
theorem reachD1_iff (r w t : ℕ) (ht : t < 3072) :
    reachD1 r w t ↔ ∃ x : PQ r, weight x = w ∧ theta x = t := by
  induction r generalizing w t with
  | zero =>
    constructor
    · rintro ⟨rfl, rfl⟩
      refine ⟨(fun _ => 0, fun _ => 0), ?_, ?_⟩
      · simp [weight, pSum, qSum]
      · simp [theta]
    · rintro ⟨x, hw, htheta⟩
      have hw0 : weight x = 0 := by simp [weight, pSum, qSum]
      have ht0 : theta x = 0 := by simp [theta]
      change w = 0 ∧ t = 0
      constructor <;> omega
  | succ r ih =>
    constructor
    · rintro ⟨_, p, q, hpq, u, htheta, hreach⟩
      have hn := thetaV_nonneg p q
      have hu : u < 3072 := by omega
      obtain ⟨x, hw, htx⟩ := (ih (w - p - 2 * q) u hu).mp hreach
      refine ⟨pqCons p q x, ?_, ?_⟩
      · rw [weight_pqCons, hw]
        omega
      · rw [theta_pqCons, htx]
        exact htheta
    · rintro ⟨x, hw, htx⟩
      let p := x.1 0
      let q := x.2 0
      let y := pqTail x
      let u := (theta y).toNat
      have huy : (u : ℤ) = theta y := Int.toNat_of_nonneg (theta_nonneg y)
      have htheta : thetaV p q + (u : ℤ) = (t : ℤ) := by
        rw [huy]
        exact (theta_head_tail x).symm.trans htx
      have hw' : p + 2 * q + weight y = w := (weight_head_tail x).symm.trans hw
      have hpq : p + 2 * q ≤ w := by omega
      have hwy : weight y = w - p - 2 * q := by omega
      have hn := thetaV_nonneg p q
      have hu : u < 3072 := by omega
      refine ⟨ht, p, q, hpq, u, htheta, ?_⟩
      exact (ih (w - p - 2 * q) u hu).mpr ⟨y, hwy, huy.symm⟩
#print axioms Paper7Pruning.reachD1_iff

/-- D2 additionally tracks the exact total number of length-two arms. -/
theorem reachD2_iff (r w Q t : ℕ) (ht : t < 3072) :
    reachD2 r w Q t ↔ ∃ x : PQ r, weight x = w ∧ qSum x = Q ∧ theta x = t := by
  induction r generalizing w Q t with
  | zero =>
    constructor
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨(fun _ => 0, fun _ => 0), ?_, ?_, ?_⟩
      · simp [weight, pSum, qSum]
      · simp [qSum]
      · simp [theta]
    · rintro ⟨x, hw, hq, htheta⟩
      have hw0 : weight x = 0 := by simp [weight, pSum, qSum]
      have hq0 : qSum x = 0 := by simp [qSum]
      have ht0 : theta x = 0 := by simp [theta]
      change w = 0 ∧ Q = 0 ∧ t = 0
      constructor
      · omega
      · constructor <;> omega
  | succ r ih =>
    constructor
    · rintro ⟨_, p, q, hpq, hqQ, u, htheta, hreach⟩
      have hn := thetaV_nonneg p q
      have hu : u < 3072 := by omega
      obtain ⟨x, hw, hq, htx⟩ := (ih (w - p - 2 * q) (Q - q) u hu).mp hreach
      refine ⟨pqCons p q x, ?_, ?_, ?_⟩
      · rw [weight_pqCons, hw]
        omega
      · rw [qSum_pqCons, hq]
        omega
      · rw [theta_pqCons, htx]
        exact htheta
    · rintro ⟨x, hw, hq, htx⟩
      let p := x.1 0
      let q := x.2 0
      let y := pqTail x
      let u := (theta y).toNat
      have huy : (u : ℤ) = theta y := Int.toNat_of_nonneg (theta_nonneg y)
      have htheta : thetaV p q + (u : ℤ) = (t : ℤ) := by
        rw [huy]
        exact (theta_head_tail x).symm.trans htx
      have hw' : p + 2 * q + weight y = w := (weight_head_tail x).symm.trans hw
      have hq' : q + qSum y = Q := (qSum_head_tail x).symm.trans hq
      have hpq : p + 2 * q ≤ w := by omega
      have hqQ : q ≤ Q := by omega
      have hwy : weight y = w - p - 2 * q := by omega
      have hqy : qSum y = Q - q := by omega
      have hn := thetaV_nonneg p q
      have hu : u < 3072 := by omega
      refine ⟨ht, p, q, hpq, hqQ, u, htheta, ?_⟩
      exact (ih (w - p - 2 * q) (Q - q) u hu).mpr ⟨y, hwy, hqy, huy.symm⟩
#print axioms Paper7Pruning.reachD2_iff

theorem reachD1_storage {r w t : ℕ} (h : reachD1 r w t) : t < 3072 := by
  cases r with
  | zero =>
    have ht : t = 0 := h.2
    omega
  | succ r => exact h.1
#print axioms Paper7Pruning.reachD1_storage

theorem reachD2_storage {r w Q t : ℕ} (h : reachD2 r w Q t) : t < 3072 := by
  cases r with
  | zero =>
    have ht : t = 0 := h.2.2
    omega
  | succ r => exact h.1
#print axioms Paper7Pruning.reachD2_storage

end Paper7Pruning
