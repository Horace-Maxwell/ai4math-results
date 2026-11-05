import Research.Backfill.Paper7.AlgebraicContracts

/-! The exact frozen two-state recurrence, including its zero-arm and empty
chain cases. These identities alone are not a bridge to deletion graphs. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Schwenk
open Polynomial BackfillPaper7.Challenge.Legacy.Algebra

theorem legPolynomial_zero : legPolynomial 0 0 = 1 := by
  simp [legPolynomial]
#print axioms Paper7Schwenk.legPolynomial_zero

theorem rootedLegPolynomial_zero : rootedLegPolynomial 0 0 = X := by
  simp [rootedLegPolynomial, legPolynomial]
#print axioms Paper7Schwenk.rootedLegPolynomial_zero

/-- Cross multiplication keeps the natural exponent boundary cases p=0/q=0
honest; no negative power or truncated-subtraction identity is assumed. -/
theorem rootedLegPolynomial_cleared (p q : ℕ) :
    X * (X^2 - 1) * rootedLegPolynomial p q =
      (X^2*(X^2-1) - C (p : ℤ)*(X^2-1) - C (q : ℤ)*X^2) *
        legPolynomial p q := by
  cases p with
  | zero =>
    cases q with
    | zero =>
      rw [rootedLegPolynomial_zero, legPolynomial_zero]
      simp only [Nat.cast_zero, map_zero, zero_mul, sub_zero, mul_one]
      ring
    | succ q =>
      simp only [rootedLegPolynomial, legPolynomial, Nat.cast_zero, map_zero,
        pow_zero, Nat.succ_ne_zero, ite_true, ite_false, Nat.zero_add, Nat.succ_sub_one, zero_mul, one_mul, sub_zero,
        pow_succ]
      ring
  | succ p =>
    cases q with
    | zero =>
      simp only [rootedLegPolynomial, legPolynomial, Nat.cast_zero, map_zero,
        pow_zero, ite_eq_right (Nat.succ_ne_zero p), ite_true, Nat.succ_sub_one,
        zero_mul, mul_one, sub_zero, pow_succ]
      ring
    | succ q =>
      simp only [rootedLegPolynomial, legPolynomial, ite_eq_right (Nat.succ_ne_zero p),
        ite_eq_right (Nat.succ_ne_zero q), Nat.succ_sub_one, pow_succ]
      ring
#print axioms Paper7Schwenk.rootedLegPolynomial_cleared

theorem chainPolynomial_nil : chainPolynomial [] = 1 := rfl
#print axioms Paper7Schwenk.chainPolynomial_nil

theorem chainPolynomial_singleton (a : ℕ × ℕ) :
    chainPolynomial [a] = rootedLegPolynomial a.1 a.2 := by
  simp [chainPolynomial, chainStep]
#print axioms Paper7Schwenk.chainPolynomial_singleton

theorem chainPolynomial_append_last (a : List (ℕ × ℕ)) (z : ℕ × ℕ) :
    chainPolynomial (a ++ [z]) =
      rootedLegPolynomial z.1 z.2 * chainPolynomial a -
        legPolynomial z.1 z.2 * (a.foldl chainStep (1,0)).2 := by
  simp only [chainPolynomial, List.foldl_append, List.foldl_cons, List.foldl_nil,
    chainStep]
#print axioms Paper7Schwenk.chainPolynomial_append_last

theorem chainPolynomial_append_two (a : List (ℕ × ℕ)) (y z : ℕ × ℕ) :
    chainPolynomial (a ++ [y,z]) =
      rootedLegPolynomial z.1 z.2 * chainPolynomial (a ++ [y]) -
        legPolynomial z.1 z.2 * legPolynomial y.1 y.2 * chainPolynomial a := by
  simp only [chainPolynomial, List.foldl_append, List.foldl_cons, List.foldl_nil,
    chainStep]
  ring
#print axioms Paper7Schwenk.chainPolynomial_append_two

end Paper7Schwenk
