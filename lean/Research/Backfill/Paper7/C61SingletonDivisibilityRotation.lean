import Research.Backfill.Paper7.C61SingletonDivisibility

/-! NEW SOURCE ONLY. Arbitrary singleton location by cyclic-shift induction. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Three Fin.NatCast
open scoped BigOperators Classical

theorem shift_iterate_apply {α : Type} (f : Fin 6 → α) (n : ℕ) (j : Fin 6) :
    ((shiftSix^[n]) f) j=f (j+(n : Fin 6)) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((shiftSix^[n]) f) (j+1)=f (j+(n.succ : Fin 6))
    rw [ih]
    congr 1
    simp [Nat.succ_eq_add_one, Nat.cast_add, add_comm, add_left_comm]
#print axioms Paper7C61Four.shift_iterate_apply

theorem ordinary_monodromy_iterate (p q : Fin 6 → ℕ) (m : ℝ) (n : ℕ)
    (hm : Mono 6 p q m=1) : Mono 6 ((shiftSix^[n]) p) ((shiftSix^[n]) q) m=1 := by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using
      ordinary_monodromy_shift ((shiftSix^[n]) p) ((shiftSix^[n]) q) m ih
#print axioms Paper7C61Four.ordinary_monodromy_iterate

theorem singleton_total_shift (q : Fin 6 → ℕ) : totalQ 6 (shiftSix q)=totalQ 6 q := by
  have h := total_shift (fun _ : Fin 6 => 0) q
  simpa [totalP, shiftSix] using h
#print axioms Paper7C61Four.singleton_total_shift

theorem singleton_total_iterate (q : Fin 6 → ℕ) (n : ℕ) :
    totalQ 6 ((shiftSix^[n]) q)=totalQ 6 q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [Function.iterate_succ_apply', singleton_total_shift] using ih
#print axioms Paper7C61Four.singleton_total_iterate

theorem singleton_shift_to_head (q : Fin 6 → ℕ) (k : Fin 6)
    (hq : ∀ j : Fin 6, j ≠ k → q j=0) :
    ∀ j : Fin 6, j ≠ 0 → ((shiftSix^[k.val]) q) j=0 := by
  intro j hj
  rw [shift_iterate_apply, Fin.cast_val_eq_self]
  apply hq (j+k)
  intro he
  have hj0 : j=0 := add_right_cancel (show j+k=0+k by simpa using he)
  exact hj hj0
#print axioms Paper7C61Four.singleton_shift_to_head

theorem mono_two_singleton_total_divisible_three (p q : Fin 6 → ℕ)
    (hm : Mono 6 p q 2=1) (hq : ∃ k : Fin 6, ∀ j : Fin 6, j ≠ k → q j=0) :
    3 ∣ totalQ 6 q := by
  obtain ⟨k, hk⟩ := hq
  have hd := mono_two_singleton_head_total_divisible_three
    ((shiftSix^[k.val]) p) ((shiftSix^[k.val]) q)
    (ordinary_monodromy_iterate p q 2 k.val hm) (singleton_shift_to_head q k hk)
  rwa [singleton_total_iterate] at hd
#print axioms Paper7C61Four.mono_two_singleton_total_divisible_three

theorem mono_three_singleton_total_divisible_eight (p q : Fin 6 → ℕ)
    (hm : Mono 6 p q 3=1) (hq : ∃ k : Fin 6, ∀ j : Fin 6, j ≠ k → q j=0) :
    8 ∣ totalQ 6 q := by
  obtain ⟨k, hk⟩ := hq
  have hd := mono_three_singleton_head_total_divisible_eight
    ((shiftSix^[k.val]) p) ((shiftSix^[k.val]) q)
    (ordinary_monodromy_iterate p q 3 k.val hm) (singleton_shift_to_head q k hk)
  rwa [singleton_total_iterate] at hd
#print axioms Paper7C61Four.mono_three_singleton_total_divisible_eight

end Paper7C61Four
