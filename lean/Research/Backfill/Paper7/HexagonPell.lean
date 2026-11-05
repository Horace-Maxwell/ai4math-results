import Research.Backfill.Paper7.HexagonSpectrum

set_option autoImplicit false

namespace Paper7Hexagon

open BackfillPaper7.Challenge

/-- Integral solutions of t² = 2r(r+1)+4. This is the positive branch
of (2r+1)²-2t²=-7, with its divisibility handled by the explicit recurrence. -/
def hexagonPellPair : ℕ → ℕ × ℕ
  | 0 => (2, 4)
  | n + 1 => (3 * (hexagonPellPair n).1 + 2 * (hexagonPellPair n).2 + 1,
      4 * (hexagonPellPair n).1 + 3 * (hexagonPellPair n).2 + 2)
#print axioms Paper7Hexagon.hexagonPellPair

theorem hexagon_pell_equation (n : ℕ) :
    (hexagonPellPair n).2 ^ 2 =
      2 * (hexagonPellPair n).1 * ((hexagonPellPair n).1 + 1) + 4 := by
  induction n with
  | zero => norm_num [hexagonPellPair]
  | succ n ih =>
    change (4 * (hexagonPellPair n).1 + 3 * (hexagonPellPair n).2 + 2) ^ 2 =
      2 * (3 * (hexagonPellPair n).1 + 2 * (hexagonPellPair n).2 + 1) *
        ((3 * (hexagonPellPair n).1 + 2 * (hexagonPellPair n).2 + 1) + 1) + 4
    nlinarith [ih]
#print axioms Paper7Hexagon.hexagon_pell_equation

theorem hexagon_pell_lower (n : ℕ) : n + 2 ≤ (hexagonPellPair n).1 := by
  induction n with
  | zero => norm_num [hexagonPellPair]
  | succ n ih =>
    change n + 1 + 2 ≤ 3 * (hexagonPellPair n).1 + 2 * (hexagonPellPair n).2 + 1
    omega
#print axioms Paper7Hexagon.hexagon_pell_lower

def hexagonPellParameter (n : ℕ) : ℕ :=
  (hexagonPellPair n).1 * ((hexagonPellPair n).1 + 1)
#print axioms Paper7Hexagon.hexagonPellParameter

theorem hexagon_pell_positive (n : ℕ) : 1 ≤ hexagonPellParameter n := by
  have h := hexagon_pell_lower n
  unfold hexagonPellParameter
  apply Nat.one_le_iff_ne_zero.mpr
  exact mul_ne_zero (by omega) (by omega)
#print axioms Paper7Hexagon.hexagon_pell_positive

theorem hexagon_pell_root_conditions (n : ℕ) :
    ((hexagonPellPair n).1 : ℤ) * (((hexagonPellPair n).1 : ℤ) + 1) =
      (hexagonPellParameter n : ℤ) ∧
    ((hexagonPellPair n).2 : ℤ) ^ 2 = 2 * (hexagonPellParameter n : ℤ) + 4 := by
  constructor
  · simp [hexagonPellParameter]
  · have he : ((hexagonPellPair n).2 : ℤ) ^ 2 =
        2 * ((hexagonPellPair n).1 : ℤ) * (((hexagonPellPair n).1 : ℤ) + 1) + 4 := by
      exact_mod_cast hexagon_pell_equation n
    simpa [hexagonPellParameter, mul_assoc] using he
#print axioms Paper7Hexagon.hexagon_pell_root_conditions

theorem hexagon_pell_orders_unbounded (n : ℕ) : n < 6 + 6 * hexagonPellParameter n := by
  have h := hexagon_pell_lower n
  have hsq : (hexagonPellPair n).1 ≤ (hexagonPellPair n).1 ^ 2 :=
    le_self_pow (by omega) (by decide)
  unfold hexagonPellParameter
  nlinarith [hsq]
#print axioms Paper7Hexagon.hexagon_pell_orders_unbounded

theorem hexagon_pell_integral (n : ℕ) :
    IsIntegralGraph (sunGraph 6 (HexagonFamily (hexagonPellParameter n))) := by
  obtain ⟨hr, ht⟩ := hexagon_pell_root_conditions n
  exact hexagon_integral_of_parameters (hexagonPellParameter n) (hexagon_pell_positive n)
    ((hexagonPellPair n).1 : ℤ) ((hexagonPellPair n).2 : ℤ) hr ht
#print axioms Paper7Hexagon.hexagon_pell_integral

theorem hexagon_pell_counterexample (n : ℕ) :
    IsCounterexample 6 (HexagonFamily (hexagonPellParameter n)) :=
  hexagon_counterexample_of_integral (hexagonPellParameter n)
    (hexagon_pell_positive n) (hexagon_pell_integral n)
#print axioms Paper7Hexagon.hexagon_pell_counterexample

end Paper7Hexagon
