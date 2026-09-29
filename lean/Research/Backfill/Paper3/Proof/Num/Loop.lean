import Research.Backfill.Paper3.Proof.Num.ListPoly

/-!
# The power loop and its soundness

`runSt K H T Q M` computes, for `m = 1, …, M`, the lists `A_m ≈ K^m`, `B_m ≈ H^{⌊m/2⌋}` and
`G_m ≈ H^{⌊m/2⌋} K^{m mod 2}` (all truncated below degree `T`), and checks for every query
`(t, c) ∈ Q m` that the comparison code (`cmpN`: `0` for `<`, `1` for `=`, `2` for `>`) of the prefix
sums up to `t` of `A_m` and `G_m` is `c`. `runSt_spec` proves by induction on `M` that a successful
run gives the same comparison codes for the prefix sums of the true polynomial powers.
-/

set_option autoImplicit false

namespace P3Num

open Finset Polynomial

/-- Comparison code: `0` if `a < b`, `1` if `a = b`, `2` if `b < a`. -/
def cmpN (a b : ℕ) : ℕ :=
  cond (Nat.blt a b) 0 (cond (Nat.beq a b) 1 2)

theorem cmpN_eq_zero_iff (a b : ℕ) : cmpN a b = 0 ↔ a < b := by
  unfold cmpN
  cases h1 : Nat.blt a b
  · have hn : ¬ a < b := fun h => by
      rw [Eq.mpr Nat.blt_eq h] at h1
      exact Bool.noConfusion h1
    cases Nat.beq a b <;> simp [hn]
  · simp [Eq.mp Nat.blt_eq h1]

theorem cmpN_eq_two_iff (a b : ℕ) : cmpN a b = 2 ↔ b < a := by
  unfold cmpN
  cases h1 : Nat.blt a b
  · have hn : ¬ a < b := fun h => by
      rw [Eq.mpr Nat.blt_eq h] at h1
      exact Bool.noConfusion h1
    cases h2 : Nat.beq a b
    · have hne : a ≠ b := fun h => by
        rw [Eq.mpr Nat.beq_eq h] at h2
        exact Bool.noConfusion h2
      change (2 : ℕ) = 2 ↔ b < a
      exact ⟨fun _ => by omega, fun _ => rfl⟩
    · have he : a = b := Eq.mp Nat.beq_eq h2
      change (1 : ℕ) = 2 ↔ b < a
      exact ⟨fun h => absurd h (by decide), fun h => by omega⟩
  · have h := Eq.mp Nat.blt_eq h1
    change (0 : ℕ) = 2 ↔ b < a
    exact ⟨fun h' => absurd h' (by decide), fun h' => by omega⟩

/-- Check all queries `(t, c)` of `qs` against the prefix sums of `A` and `G`. -/
def checkQ (A G : List ℕ) (qs : List (ℕ × ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => and (Nat.beq (cmpN (sumL (takeL (Nat.succ q.1) A))
      (sumL (takeL (Nat.succ q.1) G))) q.2) ih) qs

theorem checkQ_sound (A G : List ℕ) (qs : List (ℕ × ℕ)) (h : checkQ A G qs = true) :
    ∀ q ∈ qs, cmpN (sumL (takeL (q.1 + 1) A)) (sumL (takeL (q.1 + 1) G)) = q.2 := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have h' : (Nat.beq (cmpN (sumL (takeL (q.1 + 1) A)) (sumL (takeL (q.1 + 1) G))) q.2 &&
        checkQ A G qs) = true := h
    rw [Bool.and_eq_true, Nat.beq_eq] at h'
    intro q' hq'
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact h'.1
    · exact ih h'.2 q' hq'

/-- Loop state: `A ≈ K^m`, `B ≈ H^{⌊m/2⌋}`, and whether all checks so far succeeded. -/
structure St where
  A : List ℕ
  B : List ℕ
  ok : Bool

/-- `B_{m}` from `B_{m-1}`: multiply by `H` when `m` is even. -/
def bOf (H : List ℕ) (T m : ℕ) (B : List ℕ) : List ℕ :=
  cond (Nat.beq (Nat.mod m 2) 0) (takeL T (mulL H B)) B

/-- `G_m` from `B_m`: multiply by `K` when `m` is odd. -/
def gOf (K : List ℕ) (T m : ℕ) (B : List ℕ) : List ℕ :=
  cond (Nat.beq (Nat.mod m 2) 0) B (takeL T (mulL K B))

/-- One step `m ↦ m + 1`. -/
def step (K H : List ℕ) (T : ℕ) (Q : ℕ → List (ℕ × ℕ)) (m : ℕ) (s : St) : St :=
  let A := takeL T (mulL K s.A)
  let B := bOf H T (Nat.succ m) s.B
  ⟨A, B, and s.ok (checkQ A (gOf K T (Nat.succ m) B) (Q (Nat.succ m)))⟩

/-- The state after `M` steps. -/
def runSt (K H : List ℕ) (T : ℕ) (Q : ℕ → List (ℕ × ℕ)) (M : ℕ) : St :=
  Nat.rec (motive := fun _ => St) ⟨[1], [1], true⟩ (fun m s => step K H T Q m s) M

theorem approx_bOf {H B : List ℕ} {T m : ℕ} (hB : Approx T B (toPoly H ^ (m / 2))) :
    Approx T (bOf H T (m + 1) B) (toPoly H ^ ((m + 1) / 2)) := by
  unfold bOf
  rcases Nat.mod_two_eq_zero_or_one (m + 1) with h | h
  · have e : Nat.mod (m + 1) 2 = 0 := h
    rw [e, show (m + 1) / 2 = m / 2 + 1 by omega, pow_succ']
    exact approx_mul (approx_toPoly T H) hB
  · have e : Nat.mod (m + 1) 2 = 1 := h
    rw [e, show (m + 1) / 2 = m / 2 by omega]
    exact hB

theorem approx_gOf {K B : List ℕ} {H : ℤ[X]} {T m : ℕ} (hB : Approx T B (H ^ (m / 2))) :
    Approx T (gOf K T m B) (H ^ (m / 2) * toPoly K ^ (m % 2)) := by
  unfold gOf
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have e : Nat.mod m 2 = 0 := h
    rw [e, h, pow_zero, mul_one]
    exact hB
  · have e : Nat.mod m 2 = 1 := h
    rw [e, h, pow_one, mul_comm]
    exact approx_mul (approx_toPoly T K) hB

/-- Soundness of the loop. -/
theorem runSt_spec (K H : List ℕ) (T : ℕ) (Q : ℕ → List (ℕ × ℕ)) (M : ℕ) :
    Approx T (runSt K H T Q M).A (toPoly K ^ M) ∧
    Approx T (runSt K H T Q M).B (toPoly H ^ (M / 2)) ∧
    ((runSt K H T Q M).ok = true → ∀ m, 1 ≤ m → m ≤ M → ∀ q ∈ Q m, q.1 < T →
      cmpN (prefN (toPoly K ^ m) q.1)
        (prefN (toPoly H ^ (m / 2) * toPoly K ^ (m % 2)) q.1) = q.2) := by
  induction M with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show Approx T [1] (toPoly K ^ 0)
      rw [pow_zero]
      exact approx_one T
    · show Approx T [1] (toPoly H ^ (0 / 2))
      rw [Nat.zero_div, pow_zero]
      exact approx_one T
    · intro _ m h1 h2
      omega
  | succ M ih =>
    obtain ⟨hA, hB, hok⟩ := ih
    have hA' : Approx T (takeL T (mulL K (runSt K H T Q M).A)) (toPoly K ^ (M + 1)) := by
      rw [pow_succ']
      exact approx_mul (approx_toPoly T K) hA
    have hB' := approx_bOf (m := M) hB
    have hG' := approx_gOf (K := K) hB'
    refine ⟨hA', hB', ?_⟩
    intro hok' m h1 h2 q hq hqT
    have e : (runSt K H T Q (M + 1)).ok = ((runSt K H T Q M).ok &&
        checkQ (takeL T (mulL K (runSt K H T Q M).A))
          (gOf K T (M + 1) (bOf H T (M + 1) (runSt K H T Q M).B)) (Q (M + 1))) := rfl
    rw [e, Bool.and_eq_true] at hok'
    rcases Nat.lt_or_ge m (M + 1) with hlt | hge
    · exact hok hok'.1 m h1 (by omega) q hq hqT
    · obtain rfl : m = M + 1 := by omega
      have := checkQ_sound _ _ _ hok'.2 q hq
      rwa [sumL_takeL_eq_prefN hA' hqT, sumL_takeL_eq_prefN hG' hqT] at this

/-- The entry of index `i` of a list (`1` past the end). -/
def nthL (a : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1)
    (fun x _ ih i => Nat.rec (motive := fun _ => ℕ) x (fun j _ => ih j) i) a

end P3Num
