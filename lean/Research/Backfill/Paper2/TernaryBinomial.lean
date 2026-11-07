import Research.Backfill.Paper2.Challenge

/-! Rational binomial recurrence. Exact integer division is postponed until an
integral algebraic series has supplied a proved integer coefficient. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.TernaryBinomial

def q (k : ℕ) : ℚ := ((3 * k).choose k : ℚ) / (2 * (k : ℚ) + 1)

theorem q_zero : q 0 = 1 := by norm_num [q]

theorem choose_ratio (k : ℕ) :
    (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 1) * ((3 * k + 3).choose (k + 1) : ℚ) =
      3 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 2) * ((3 * k).choose k : ℚ) := by
  have h0 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 3 * k by omega)
  rw [show 3 * k - k = 2 * k by omega] at h0
  have h1 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ 3 * k + 3 by omega)
  rw [show 3 * k + 3 - (k + 1) = 2 * k + 2 by omega] at h1
  have h0q : ((3 * k).choose k : ℚ) * (k.factorial : ℚ) * ((2 * k).factorial : ℚ) =
      ((3 * k).factorial : ℚ) := by exact_mod_cast h0
  have h1q : ((3 * k + 3).choose (k + 1) : ℚ) * ((k + 1).factorial : ℚ) *
      ((2 * k + 2).factorial : ℚ) = ((3 * k + 3).factorial : ℚ) := by exact_mod_cast h1
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h1q
  have hz : ((2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 1) *
        ((3 * k + 3).choose (k + 1) : ℚ) -
        3 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 2) * ((3 * k).choose k : ℚ)) *
      (((k + 1 : ℕ) : ℚ) * (k.factorial : ℚ) * ((2 * k).factorial : ℚ)) = 0 := by
    push_cast
    linear_combination h1q -
      (3 * ((k : ℚ) + 1) * (3 * (k : ℚ) + 2) * (3 * (k : ℚ) + 1)) * h0q
  have hne : (((k + 1 : ℕ) : ℚ) * (k.factorial : ℚ) * ((2 * k).factorial : ℚ)) ≠ 0 := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hne)

theorem q_mul_den (k : ℕ) :
    (2 * (k : ℚ) + 1) * q k = ((3 * k).choose k : ℚ) := by
  have hn : 2 * (k : ℚ) + 1 ≠ 0 := by positivity
  dsimp only [q]
  field_simp

theorem q_recurrence (k : ℕ) :
    (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 2) * q (k + 1) =
      3 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 2) * q k := by
  have hnext : (2 * (k : ℚ) + 3) * q (k + 1) =
      ((3 * k + 3).choose (k + 1) : ℚ) := by
    have he := q_mul_den (k + 1)
    rw [show 3 * (k + 1) = 3 * k + 3 by omega] at he
    push_cast at he
    linear_combination he
  have hn : 2 * (k : ℚ) + 1 ≠ 0 := by positivity
  apply mul_right_cancel₀ hn
  calc
    ((2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 2) * q (k + 1)) * (2 * (k : ℚ) + 1) =
        (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 1) * ((2 * (k : ℚ) + 3) * q (k + 1)) := by ring
    _ = (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 1) * ((3 * k + 3).choose (k + 1) : ℚ) := by rw [hnext]
    _ = 3 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 2) * ((3 * k).choose k : ℚ) := choose_ratio k
    _ = (3 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 2) * q k) * (2 * (k : ℚ) + 1) := by
      rw [← q_mul_den k]
      ring

end BackfillPaper2.TernaryBinomial
#print axioms BackfillPaper2.TernaryBinomial.q_zero
#print axioms BackfillPaper2.TernaryBinomial.choose_ratio
#print axioms BackfillPaper2.TernaryBinomial.q_mul_den
#print axioms BackfillPaper2.TernaryBinomial.q_recurrence
