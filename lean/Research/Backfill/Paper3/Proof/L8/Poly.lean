import Mathlib

/-!
# Lemma 8, part 1: generating polynomials and a Chebyshev bound for their powers

For weights `a : ℕ → ℝ` put `gpoly a M = Σ_{i ≤ M} a i X^i`. If the coefficients of `g` are
nonnegative with `g(1) = 1`, the coefficients of `g^m` are the law of a sum of `m` i.i.d.
variables whose law is given by the coefficients of `g`; we prove the moment identities
`Σ_s [z^s] g^m = 1`, `Σ_s s [z^s] g^m = m g'(1)` and
`Σ_s (s - m g'(1))² [z^s] g^m = m (g''(1) + g'(1) - g'(1)²)` (product rule for `derivative`),
and deduce the Chebyshev bound for the mass of the window `|s - m g'(1)| < r`.
-/

set_option autoImplicit false

namespace P3L8

open Polynomial Finset

/-- The generating polynomial `Σ_{i ≤ M} a i X^i` of the weights `a`. -/
noncomputable def gpoly (a : ℕ → ℝ) (M : ℕ) : ℝ[X] := ∑ i ∈ range (M + 1), C (a i) * X ^ i

theorem coeff_gpoly (a : ℕ → ℝ) (M n : ℕ) :
    (gpoly a M).coeff n = if n ∈ range (M + 1) then a n else 0 := by
  unfold gpoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]

theorem natDegree_gpoly_le (a : ℕ → ℝ) (M : ℕ) : (gpoly a M).natDegree ≤ M := by
  unfold gpoly
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_X_pow_le (a i) i).trans (Nat.lt_succ_iff.mp (mem_range.mp hi))

theorem natDegree_gpoly_pow_lt (a : ℕ → ℝ) (M m : ℕ) :
    (gpoly a M ^ m).natDegree < m * M + 1 := by
  have h1 := natDegree_pow_le (p := gpoly a M) (n := m)
  have h2 := Nat.mul_le_mul_left m (natDegree_gpoly_le a M)
  omega

theorem coeff_gpoly_nonneg (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (M n : ℕ) :
    0 ≤ (gpoly a M).coeff n := by
  rw [coeff_gpoly]
  split_ifs
  · exact ha n
  · exact le_refl 0

theorem coeff_gpoly_pow_nonneg (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℕ) :
    ∀ m s : ℕ, 0 ≤ (gpoly a M ^ m).coeff s := by
  intro m
  induction m with
  | zero =>
    intro s
    rw [pow_zero, coeff_one]
    split_ifs <;> norm_num
  | succ m ih =>
    intro s
    rw [pow_succ, coeff_mul]
    apply sum_nonneg
    intro z _
    exact mul_nonneg (ih _) (coeff_gpoly_nonneg a ha M _)

theorem eval_one_gpoly (a : ℕ → ℝ) (M : ℕ) : (gpoly a M).eval 1 = ∑ i ∈ range (M + 1), a i := by
  unfold gpoly
  rw [eval_finsetSum]
  simp

/-! ### Moments of the coefficients via derivatives at `1` -/

theorem sum_coeff_eq_eval (G : ℝ[X]) (n : ℕ) (hn : G.natDegree < n) :
    ∑ s ∈ range n, G.coeff s = G.eval 1 := by
  rw [eval_eq_sum_range' hn]
  simp

theorem sum_mul_coeff_eq (G : ℝ[X]) (n : ℕ) (hn : G.natDegree < n) :
    ∑ s ∈ range n, (s : ℝ) * G.coeff s = (derivative G).eval 1 := by
  rw [derivative_eval,
    sum_over_range' G (f := fun k c => c * (k : ℝ) * (1 : ℝ) ^ (k - 1)) (fun k => by simp) n hn]
  apply sum_congr rfl
  intro s _
  simp only [one_pow, mul_one]
  ring

theorem sum_mul_pred_coeff_eq (G : ℝ[X]) (n : ℕ) (hn : G.natDegree < n) :
    ∑ s ∈ range n, (s : ℝ) * ((s : ℝ) - 1) * G.coeff s = (derivative (derivative G)).eval 1 := by
  have hn' : (derivative G).natDegree < n :=
    lt_of_le_of_lt ((natDegree_derivative_le G).trans (Nat.sub_le _ _)) hn
  rw [← sum_mul_coeff_eq _ n hn']
  simp only [coeff_derivative]
  have hc : G.coeff n = 0 := coeff_eq_zero_of_natDegree_lt hn
  calc ∑ s ∈ range n, (s : ℝ) * ((s : ℝ) - 1) * G.coeff s
      = ∑ s ∈ range (n + 1), (s : ℝ) * ((s : ℝ) - 1) * G.coeff s := by
        rw [sum_range_succ, hc, mul_zero, add_zero]
    _ = ∑ s ∈ range n, ((s + 1 : ℕ) : ℝ) * (((s + 1 : ℕ) : ℝ) - 1) * G.coeff (s + 1) + 0 := by
        rw [sum_range_succ']
        simp
    _ = ∑ s ∈ range n, (s : ℝ) * (G.coeff (s + 1) * ((s : ℝ) + 1)) := by
        rw [add_zero]
        apply sum_congr rfl
        intro s _
        push_cast
        ring

theorem eval_one_pow (g : ℝ[X]) (h0 : g.eval 1 = 1) (m : ℕ) : (g ^ m).eval 1 = 1 := by
  rw [eval_pow, h0, one_pow]

theorem eval_one_derivative_pow (g : ℝ[X]) (h0 : g.eval 1 = 1) (m : ℕ) :
    (derivative (g ^ m)).eval 1 = m * (derivative g).eval 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, derivative_mul]
    simp only [eval_add, eval_mul]
    rw [ih, eval_one_pow g h0 m, h0]
    push_cast
    ring

theorem eval_one_derivative2_pow (g : ℝ[X]) (h0 : g.eval 1 = 1) (m : ℕ) :
    (derivative (derivative (g ^ m))).eval 1 =
      m * (derivative (derivative g)).eval 1 + ((m : ℝ) ^ 2 - m) * ((derivative g).eval 1) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, derivative_mul, map_add, derivative_mul, derivative_mul]
    simp only [eval_add, eval_mul]
    rw [ih, eval_one_derivative_pow g h0 m, eval_one_pow g h0 m, h0]
    push_cast
    ring

/-- The second central moment of the coefficients of `g^m`. -/
theorem sum_sq_dev (g : ℝ[X]) (h0 : g.eval 1 = 1) (m n : ℕ) (hn : (g ^ m).natDegree < n) :
    ∑ s ∈ range n, ((s : ℝ) - m * (derivative g).eval 1) ^ 2 * (g ^ m).coeff s =
      m * ((derivative (derivative g)).eval 1 + (derivative g).eval 1 -
        ((derivative g).eval 1) ^ 2) := by
  set μ := (derivative g).eval 1 with hμ
  set t := (derivative (derivative g)).eval 1 with ht
  have e0 := sum_coeff_eq_eval (g ^ m) n hn
  have e1 := sum_mul_coeff_eq (g ^ m) n hn
  have e2 := sum_mul_pred_coeff_eq (g ^ m) n hn
  rw [eval_one_pow g h0] at e0
  rw [eval_one_derivative_pow g h0] at e1
  rw [eval_one_derivative2_pow g h0] at e2
  have hsplit : ∀ s ∈ range n, ((s : ℝ) - m * μ) ^ 2 * (g ^ m).coeff s =
      (s : ℝ) * ((s : ℝ) - 1) * (g ^ m).coeff s + (1 - 2 * m * μ) * ((s : ℝ) * (g ^ m).coeff s) +
        (m * μ) ^ 2 * (g ^ m).coeff s := by
    intro s _
    ring
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, e0, e1, e2]
  ring

/-- Chebyshev: the mass of the window `|s - μ| < r` is at least `1 - V / r²`. -/
theorem sum_window_ge (c : ℕ → ℝ) (hc : ∀ s, 0 ≤ c s) (n : ℕ) (μ r V : ℝ) (hr : 0 < r)
    (h1 : ∑ s ∈ range n, c s = 1) (hV : ∑ s ∈ range n, ((s : ℝ) - μ) ^ 2 * c s ≤ V) :
    1 - V / r ^ 2 ≤ ∑ s ∈ (range n).filter (fun s : ℕ => |(s : ℝ) - μ| < r), c s := by
  have hsplit := sum_filter_add_sum_filter_not (range n) (fun s : ℕ => |(s : ℝ) - μ| < r) c
  have hfar : ∑ s ∈ (range n).filter (fun s : ℕ => ¬ |(s : ℝ) - μ| < r), c s ≤ V / r ^ 2 := by
    rw [le_div_iff₀ (by positivity), sum_mul]
    calc ∑ s ∈ (range n).filter (fun s : ℕ => ¬ |(s : ℝ) - μ| < r), c s * r ^ 2
        ≤ ∑ s ∈ (range n).filter (fun s : ℕ => ¬ |(s : ℝ) - μ| < r), ((s : ℝ) - μ) ^ 2 * c s := by
          apply sum_le_sum
          intro s hs
          rw [mem_filter, not_lt] at hs
          have hsq : r ^ 2 ≤ ((s : ℝ) - μ) ^ 2 := by
            rw [← sq_abs ((s : ℝ) - μ)]
            exact pow_le_pow_left₀ hr.le hs.2 2
          have := hc s
          nlinarith
      _ ≤ ∑ s ∈ range n, ((s : ℝ) - μ) ^ 2 * c s := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro s _ _
          exact mul_nonneg (sq_nonneg _) (hc s)
      _ ≤ V := hV
  linarith

end P3L8
