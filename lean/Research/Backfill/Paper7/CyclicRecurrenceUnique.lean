import Research.Backfill.Paper7.ChallengeV3

set_option autoImplicit false

namespace Paper7Lemma22Periodic

open BackfillPaper7.Challenge

/-- The actual cyclic successor agrees with addition before the wrap point. -/
theorem nxt_mk_eq (b n : ℕ) (hn : n < b) (hn1 : n + 1 < b) :
    nxt b ⟨n, hn⟩ = ⟨n + 1, hn1⟩ := by
  let : NeZero b := ⟨by omega⟩
  apply Fin.ext
  rw [nxt, finRotate_apply]
  exact Fin.val_add_one_of_lt' hn1
#print axioms Paper7Lemma22Periodic.nxt_mk_eq

/-- Two zero initial values force every value of a real cyclic second-order
recurrence to vanish. This is an injectivity helper, not the full spectral lemma. -/
theorem cyclic_zero_of_two_values (b : ℕ) (hb : 3 ≤ b) (c y : Fin b → ℝ)
    (hy : ∀ k, y (prv b k) + y (nxt b k) = c k * y k)
    (h0 : y ⟨0, by omega⟩ = 0) (h1 : y ⟨1, by omega⟩ = 0) : y = 0 := by
  have hz : ∀ n (hn : n < b), y ⟨n, hn⟩ = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      cases n with
      | zero => exact h0
      | succ n =>
        cases n with
        | zero => exact h1
        | succ n =>
          have hz0 : y ⟨n, by omega⟩ = 0 := ih n (by omega) (by omega)
          have hz1 : y ⟨n + 1, by omega⟩ = 0 := ih (n + 1) (by omega) (by omega)
          have hp : prv b ⟨n + 1, by omega⟩ = ⟨n, by omega⟩ := by
            exact (finRotate b).symm_apply_eq.mpr
              (nxt_mk_eq b n (by omega) (by omega)).symm
          have ht := hy ⟨n + 1, by omega⟩
          rw [hp, nxt_mk_eq b (n + 1) (by omega) (by omega), hz0, hz1,
            mul_zero, zero_add] at ht
          exact ht
  funext k
  exact hz k.val k.isLt
#print axioms Paper7Lemma22Periodic.cyclic_zero_of_two_values

end Paper7Lemma22Periodic
