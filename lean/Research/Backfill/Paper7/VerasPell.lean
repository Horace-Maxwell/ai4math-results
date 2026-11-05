import Research.Backfill.Paper7.VerasSquares

set_option autoImplicit false

namespace Paper7Veras

open BackfillPaper7.Challenge

/-- Explicit positive Pell sequence, beginning with the 68-vertex member. -/
def pellPair : ℕ → ℕ × ℕ
  | 0 => (3, 2)
  | n + 1 => (3 * (pellPair n).1 + 4 * (pellPair n).2,
      2 * (pellPair n).1 + 3 * (pellPair n).2)
#print axioms Paper7Veras.pellPair

theorem pell_equation (n : ℕ) :
    (pellPair n).1 ^ 2 = 2 * (pellPair n).2 ^ 2 + 1 := by
  induction n with
  | zero => norm_num [pellPair]
  | succ n ih =>
    change (3 * (pellPair n).1 + 4 * (pellPair n).2) ^ 2 =
      2 * (2 * (pellPair n).1 + 3 * (pellPair n).2) ^ 2 + 1
    nlinarith [ih]
#print axioms Paper7Veras.pell_equation

theorem pell_lower (n : ℕ) : n + 2 ≤ (pellPair n).2 := by
  induction n with
  | zero => norm_num [pellPair]
  | succ n ih =>
    change n + 1 + 2 ≤ 2 * (pellPair n).1 + 3 * (pellPair n).2
    omega
#print axioms Paper7Veras.pell_lower

def pellParameter (n : ℕ) : ℕ := (2 * (pellPair n).2) ^ 2
#print axioms Paper7Veras.pellParameter

theorem pell_parameter_positive (n : ℕ) : 1 ≤ pellParameter n := by
  have h := pell_lower n
  change 1 ≤ (2 * (pellPair n).2) ^ 2
  apply Nat.one_le_iff_ne_zero.mpr
  exact pow_ne_zero 2 (by omega)
#print axioms Paper7Veras.pell_parameter_positive

theorem pell_square_conditions (n : ℕ) :
    ((2 * (pellPair n).2 : ℕ) : ℤ) ^ 2 = (pellParameter n : ℤ) ∧
      ((2 * (pellPair n).1 : ℕ) : ℤ) ^ 2 = 2 * (pellParameter n : ℤ) + 4 := by
  constructor
  · simp [pellParameter]
  · have he : ((pellPair n).1 : ℤ) ^ 2 = 2 * ((pellPair n).2 : ℤ) ^ 2 + 1 := by
      exact_mod_cast pell_equation n
    norm_num [pellParameter]
    nlinarith [he]
#print axioms Paper7Veras.pell_square_conditions

theorem pell_orders_unbounded (n : ℕ) : n < 4 + 4 * pellParameter n := by
  have h := pell_lower n
  have hsq : (pellPair n).2 ≤ (pellPair n).2 ^ 2 :=
    le_self_pow (by omega) (by decide)
  unfold pellParameter
  nlinarith [hsq]
#print axioms Paper7Veras.pell_orders_unbounded

theorem pell_veras_integral (n : ℕ) :
    IsIntegralGraph (sunGraph 4 (VerasSquare (pellParameter n))) := by
  obtain ⟨hu, hv⟩ := pell_square_conditions n
  exact veras_integral_of_squares (pellParameter n) (pell_parameter_positive n)
    ((2 * (pellPair n).2 : ℕ) : ℤ) ((2 * (pellPair n).1 : ℕ) : ℤ) hu hv
#print axioms Paper7Veras.pell_veras_integral

end Paper7Veras
