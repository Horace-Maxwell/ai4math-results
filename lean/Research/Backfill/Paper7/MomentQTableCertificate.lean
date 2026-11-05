import Research.Backfill.Paper7.BoundedQSumDP

/-! A finite table is accepted only through all its initial and successor cell
equations. No concrete table or numeric total is an assumption of a main goal.
Source-only candidate, not compiled. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCertificate
open Paper7MomentDP
open scoped BigOperators

def qTableRemainder {T : ℕ} (t : Fin (T + 1)) (a : ℕ) : Fin (T + 1) :=
  ⟨t.val - a, lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩
#print axioms Paper7MomentCertificate.qTableRemainder

def qTablePrefix {n : ℕ} (z : Fin n → ℕ) (k : ℕ) (hk : k ≤ n) : Fin k → ℕ :=
  fun i => z ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
#print axioms Paper7MomentCertificate.qTablePrefix

theorem qTablePrefix_self {n : ℕ} (z : Fin n → ℕ) :
    qTablePrefix z n (Nat.le_refl n) = z := by
  funext i
  rfl
#print axioms Paper7MomentCertificate.qTablePrefix_self

def QTableValid {n T : ℕ} (z : Fin n → ℕ)
    (L : Fin (n + 1) → Fin (T + 1) → ℕ) : Prop :=
  (∀ t, L 0 t = if t.val = 0 then 1 else 0) ∧
  ∀ k : Fin n, ∀ t,
    L k.succ t = ∑ a : Fin (z k + 1),
      if a.val ≤ t.val then L k.castSucc (qTableRemainder t a.val) else 0
#print axioms Paper7MomentCertificate.QTableValid

/-- Every checked prefix cell equals the actual bounded-sum fibre recurrence. -/
theorem qTable_sound {n T : ℕ} (z : Fin n → ℕ)
    (L : Fin (n + 1) → Fin (T + 1) → ℕ) (hL : QTableValid z L) :
    ∀ k (hk : k ≤ n) (t : Fin (T + 1)),
      L ⟨k, Nat.lt_succ_of_le hk⟩ t =
        boundedQDP k (qTablePrefix z k hk) t.val := by
  intro k
  induction k with
  | zero =>
    intro hk t
    rw [boundedQDP_zero]
    exact hL.1 t
  | succ k ih =>
    intro hk t
    have hkn : k < n := Nat.lt_of_succ_le hk
    have hkle : k ≤ n := Nat.le_of_lt hkn
    calc
      L ⟨k + 1, Nat.lt_succ_of_le hk⟩ t =
          ∑ a : Fin (z ⟨k, hkn⟩ + 1),
            if a.val ≤ t.val then
              L ⟨k, Nat.lt_succ_of_le hkle⟩ (qTableRemainder t a.val) else 0 :=
        hL.2 ⟨k, hkn⟩ t
      _ = ∑ a : Fin (z ⟨k, hkn⟩ + 1),
          if a.val ≤ t.val then
            boundedQDP k (qTablePrefix z k hkle) (t.val - a.val) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a.val ≤ t.val
        · simp only [ha, ite_true]
          exact ih hkle (qTableRemainder t a.val)
        · simp only [ha, ite_false]
      _ = boundedQDP (k + 1) (qTablePrefix z (k + 1) hk) t.val := by
        rw [boundedQDP_snoc]
        rfl
#print axioms Paper7MomentCertificate.qTable_sound

theorem qTable_last_eq {n T : ℕ} (z : Fin n → ℕ)
    (L : Fin (n + 1) → Fin (T + 1) → ℕ) (hL : QTableValid z L)
    (t : Fin (T + 1)) : L (Fin.last n) t = boundedQDP n z t.val := by
  change L ⟨n, Nat.lt_succ_self n⟩ t = boundedQDP n z t.val
  simpa only [qTablePrefix_self] using qTable_sound z L hL n (Nat.le_refl n) t
#print axioms Paper7MomentCertificate.qTable_last_eq

end Paper7MomentCertificate
