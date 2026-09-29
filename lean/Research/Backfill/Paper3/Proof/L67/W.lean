import Research.Backfill.Paper3.Proof.Poly

/-!
# The polynomials `W_{αβ}`: symmetry, real values, low coefficients

`W_{αβ}(z) = Σ_{i,j<d} C(d-1,i) C(d-1,j) z^{ij + αj + βi}`. We prove `W₁₀ = W₀₁` (`WSymm`, by
exchanging the two summation indices), the value of `W_{αβ}` at a real point, and the
coefficients of `z^0` and `z^1` of `W₀₀`, `W₁₁`, `W₁₀` (write `d = n + 1`; peel off the index `0`
of each sum; only the terms with exponent `0` or `1` survive).
-/

set_option autoImplicit false

namespace P3L67

open Finset Polynomial BackfillPaper3.Challenge

/-- `W₁₀ = W₀₁`: exchange the summation indices. -/
theorem wSymm (d : ℕ) : Wpoly d 1 0 = Wpoly d 0 1 := by
  unfold Wpoly
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.mul_comm ((d - 1).choose j), show j * i + 1 * i + 0 * j = i * j + 0 * j + 1 * i by ring]

/-- The value of `W_{αβ}` at a real point. -/
theorem evalR_Wpoly (d α β : ℕ) (q : ℝ) : evalR (Wpoly d α β) q =
    ∑ i ∈ range d, ∑ j ∈ range d,
      ((d - 1).choose i : ℝ) * ((d - 1).choose j : ℝ) * q ^ (i * j + α * j + β * i) := by
  simp [evalR, Wpoly]

/-- The coefficients of `W_{αβ}`. -/
theorem coeff_Wpoly (d α β t : ℕ) : (Wpoly d α β).coeff t =
    ∑ i ∈ range d, ∑ j ∈ range d,
      if t = i * j + α * j + β * i then (((d - 1).choose i * (d - 1).choose j : ℕ) : ℤ) else 0 := by
  unfold Wpoly
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]

theorem sum_choose_succ (n : ℕ) : (∑ x ∈ range n, (n.choose (x + 1) : ℤ)) + 1 = 2 ^ n := by
  have h := Nat.sum_range_choose n
  rw [Finset.sum_range_succ', Nat.choose_zero_right] at h
  exact_mod_cast h

theorem one_eq_mul_iff (a b : ℕ) : 1 = (a + 1) * (b + 1) ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    rfl

theorem one_ne_mul_add_add (a b : ℕ) : ¬ 1 = (a + 1) * (b + 1) + (b + 1) + (a + 1) := by
  intro h
  nlinarith

theorem one_ne_mul_add (a b : ℕ) : ¬ 1 = (a + 1) * (b + 1) + (b + 1) := by
  intro h
  nlinarith

theorem coeff_W00_zero (n : ℕ) : (Wpoly (n + 1) 0 0).coeff 0 = 2 ^ (n + 1) - 1 := by
  rw [coeff_Wpoly]
  simp [Finset.sum_range_succ']
  have := sum_choose_succ n
  rw [pow_succ]
  linarith

theorem coeff_W11_zero (n : ℕ) : (Wpoly (n + 1) 1 1).coeff 0 = 1 := by
  rw [coeff_Wpoly]
  simp [Finset.sum_range_succ']

theorem coeff_W10_zero (n : ℕ) : (Wpoly (n + 1) 1 0).coeff 0 = 2 ^ n := by
  rw [coeff_Wpoly]
  simp [Finset.sum_range_succ']
  exact sum_choose_succ n

theorem coeff_W00_one (n : ℕ) (hn : 0 < n) : (Wpoly (n + 1) 0 0).coeff 1 = n ^ 2 := by
  rw [coeff_Wpoly]
  simp [Finset.sum_range_succ', one_eq_mul_iff, hn, ite_and]
  ring

theorem coeff_W11_one (n : ℕ) (hn : 0 < n) : (Wpoly (n + 1) 1 1).coeff 1 = 2 * n := by
  rw [coeff_Wpoly]
  simp [Finset.sum_range_succ', one_ne_mul_add_add, hn]
  ring

theorem coeff_W10_one (n : ℕ) (hn : 0 < n) : (Wpoly (n + 1) 1 0).coeff 1 = n := by
  rw [coeff_Wpoly]
  simp [Finset.sum_range_succ', one_ne_mul_add, hn]

end P3L67
