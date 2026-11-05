import Research.Backfill.Paper7.GapFirstHit

/-! Exact zero-recurrence values on a path with the left Dirichlet value zero.
All finite-segment uniqueness and the right-end parity constraint are proved. -/
set_option autoImplicit false
noncomputable section

namespace Paper7Lemma22Gaps

def zeroDirichletValue (a : ℝ) (n : ℕ) : ℝ :=
  if n % 4 = 0 then 0 else if n % 4 = 1 then a else if n % 4 = 2 then 0 else -a
#print axioms Paper7Lemma22Gaps.zeroDirichletValue

theorem zeroDirichletValue_zero (a : ℝ) : zeroDirichletValue a 0 = 0 := by
  norm_num [zeroDirichletValue]
#print axioms Paper7Lemma22Gaps.zeroDirichletValue_zero

theorem zeroDirichletValue_one (a : ℝ) : zeroDirichletValue a 1 = a := by
  norm_num [zeroDirichletValue]
#print axioms Paper7Lemma22Gaps.zeroDirichletValue_one

theorem zeroDirichletValue_recurrence (a : ℝ) (n : ℕ) :
    zeroDirichletValue a n + zeroDirichletValue a (n + 2) = 0 := by
  have hn : n % 4 < 4 := Nat.mod_lt n (by decide)
  rcases (show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega) with h | h | h | h <;>
    norm_num [zeroDirichletValue, Nat.add_mod, h]
#print axioms Paper7Lemma22Gaps.zeroDirichletValue_recurrence

theorem zeroDirichletValue_eq_zero_iff (a : ℝ) (n : ℕ) :
    zeroDirichletValue a n = 0 ↔ Even n ∨ a = 0 := by
  have hn : n % 4 < 4 := Nat.mod_lt n (by decide)
  rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
  rcases (show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega) with h | h | h | h
  · have h2 : n % 2 = 0 := by omega
    simp [zeroDirichletValue, h, h2]
  · have h2 : n % 2 = 1 := by omega
    simp [zeroDirichletValue, h, h2]
  · have h2 : n % 2 = 0 := by omega
    simp [zeroDirichletValue, h, h2]
  · have h2 : n % 2 = 1 := by omega
    simp [zeroDirichletValue, h, h2]
#print axioms Paper7Lemma22Gaps.zeroDirichletValue_eq_zero_iff

/-- The two initial values determine the actual recurrence on the entire
finite segment through d; no endpoint/surjectivity hypothesis is added. -/
theorem zeroDirichlet_unique (d : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0)
    (hr : ∀ n : ℕ, n + 2 ≤ d → f n + f (n + 2) = 0) :
    ∀ n : ℕ, n ≤ d → f n = zeroDirichletValue (f 1) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simpa only [zeroDirichletValue_zero] using h0
    | succ n =>
      cases n with
      | zero => exact (zeroDirichletValue_one (f 1)).symm
      | succ n =>
        have hprev := ih n (by omega) (by omega)
        have hrec := hr n (by omega)
        have hval := zeroDirichletValue_recurrence (f 1) n
        linarith
#print axioms Paper7Lemma22Gaps.zeroDirichlet_unique

theorem zeroDirichlet_right_endpoint (d : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0)
    (hr : ∀ n : ℕ, n + 2 ≤ d → f n + f (n + 2) = 0) :
    f d = 0 ↔ Even d ∨ f 1 = 0 := by
  rw [zeroDirichlet_unique d f h0 hr d le_rfl, zeroDirichletValue_eq_zero_iff]
#print axioms Paper7Lemma22Gaps.zeroDirichlet_right_endpoint

end Paper7Lemma22Gaps
