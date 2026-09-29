import Research.Backfill.Paper3.Proof.L8.Poly

/-!
# Lemma 8, part 2: exponential tilting and the window bound

For weights `a ≥ 0` with `a 0 > 0` and `λ ∈ ℝ` let `Z(λ) = Σ_{i ≤ M} a i e^{λ i}` and let
`tilt a M λ i = a i e^{λ i} / Z(λ)` be the tilted weights, with mean `tmean a M λ`. Then
`[z^s] f^m = Z(λ)^m e^{-λ s} [z^s] g^m` (`f = gpoly a M`, `g = gpoly (tilt a M λ) M`), and the
Chebyshev bound for `g^m` gives, for the window `|s - m μ_λ| < m δ`,
`Σ_{window} [z^s] f^m ≥ exp(m (log Z(λ) - λ μ_λ - δ |λ|)) (1 - M² / (m δ²))`.
-/

set_option autoImplicit false

namespace P3L8

open Polynomial Finset

/-- `Z(λ) = Σ_{i ≤ M} a i e^{λ i}`. -/
noncomputable def Zf (a : ℕ → ℝ) (M : ℕ) (l : ℝ) : ℝ :=
  ∑ i ∈ range (M + 1), a i * Real.exp (l * i)

/-- The tilted weights `a i e^{λ i} / Z(λ)`. -/
noncomputable def tilt (a : ℕ → ℝ) (M : ℕ) (l : ℝ) (i : ℕ) : ℝ :=
  a i * Real.exp (l * i) / Zf a M l

/-- The mean `Σ_i i a i e^{λ i} / Z(λ)` of the tilted weights. -/
noncomputable def tmean (a : ℕ → ℝ) (M : ℕ) (l : ℝ) : ℝ :=
  (∑ i ∈ range (M + 1), (i : ℝ) * a i * Real.exp (l * i)) / Zf a M l

theorem Zf_pos (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (h0 : 0 < a 0) (l : ℝ) :
    0 < Zf a M l := by
  unfold Zf
  have hle : a 0 * Real.exp (l * ((0 : ℕ) : ℝ)) ≤ ∑ i ∈ range (M + 1), a i * Real.exp (l * i) :=
    single_le_sum (f := fun i : ℕ => a i * Real.exp (l * i))
      (fun i _ => mul_nonneg (ha i) (Real.exp_pos _).le) (mem_range.mpr (Nat.succ_pos M))
  have hpos : 0 < a 0 * Real.exp (l * ((0 : ℕ) : ℝ)) := mul_pos h0 (Real.exp_pos _)
  linarith

theorem tilt_nonneg (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (h0 : 0 < a 0) (l : ℝ) (i : ℕ) :
    0 ≤ tilt a M l i :=
  div_nonneg (mul_nonneg (ha i) (Real.exp_pos _).le) (Zf_pos a M ha h0 l).le

/-- Coefficients of powers under a change of weights `b i = a i w^i c`. -/
theorem coeff_pow_of_scale (a b : ℕ → ℝ) (M : ℕ) (w c : ℝ) (hb : ∀ i, b i = a i * w ^ i * c) :
    ∀ m s : ℕ, (gpoly b M ^ m).coeff s = (gpoly a M ^ m).coeff s * w ^ s * c ^ m := by
  intro m
  induction m with
  | zero =>
    intro s
    simp only [pow_zero, mul_one]
    by_cases h : s = 0
    · subst h
      simp
    · simp [coeff_one, h]
  | succ m ih =>
    intro s
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul, sum_mul, sum_mul]
    apply sum_congr rfl
    intro z hz
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz
    rw [ih, coeff_gpoly, coeff_gpoly]
    split_ifs
    · rw [hb, ← hz, pow_add, pow_succ]
      ring
    · ring

theorem eval_one_tilt (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (h0 : 0 < a 0) (l : ℝ) :
    (gpoly (tilt a M l) M).eval 1 = 1 := by
  rw [eval_one_gpoly]
  unfold tilt
  rw [← sum_div]
  exact div_self (Zf_pos a M ha h0 l).ne'

theorem derivative_eval_one_tilt (a : ℕ → ℝ) (M : ℕ) (l : ℝ) :
    (derivative (gpoly (tilt a M l) M)).eval 1 = tmean a M l := by
  rw [← sum_mul_coeff_eq _ (M + 1) (Nat.lt_succ_of_le (natDegree_gpoly_le _ M))]
  unfold tmean
  rw [sum_div]
  apply sum_congr rfl
  intro i hi
  rw [coeff_gpoly, ite_eq_left hi]
  unfold tilt
  ring

theorem second_moment_tilt_le (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (h0 : 0 < a 0) (l : ℝ) :
    (derivative (derivative (gpoly (tilt a M l) M))).eval 1 +
      (derivative (gpoly (tilt a M l) M)).eval 1 ≤ (M : ℝ) ^ 2 := by
  have hn := Nat.lt_succ_of_le (natDegree_gpoly_le (tilt a M l) M)
  rw [← sum_mul_pred_coeff_eq _ _ hn, ← sum_mul_coeff_eq _ _ hn, ← sum_add_distrib]
  have h1 : ∑ i ∈ range (M + 1), tilt a M l i = 1 := by
    rw [← eval_one_gpoly]
    exact eval_one_tilt a M ha h0 l
  calc ∑ s ∈ range (M + 1), ((s : ℝ) * ((s : ℝ) - 1) * (gpoly (tilt a M l) M).coeff s +
        (s : ℝ) * (gpoly (tilt a M l) M).coeff s)
      = ∑ s ∈ range (M + 1), (s : ℝ) ^ 2 * tilt a M l s := by
        apply sum_congr rfl
        intro s hs
        rw [coeff_gpoly, ite_eq_left hs]
        ring
    _ ≤ ∑ s ∈ range (M + 1), (M : ℝ) ^ 2 * tilt a M l s := by
        apply sum_le_sum
        intro s hs
        have hsM : (s : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hs)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg s) hsM 2)
          (tilt_nonneg a M ha h0 l s)
    _ = (M : ℝ) ^ 2 := by rw [← mul_sum, h1, mul_one]

/-- `[z^s] f^m = [z^s] g^m · Z(λ)^m · e^{-λ s}`. -/
theorem coeff_pow_tilt (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (h0 : 0 < a 0) (l : ℝ)
    (m s : ℕ) :
    (gpoly a M ^ m).coeff s =
      (gpoly (tilt a M l) M ^ m).coeff s * Zf a M l ^ m * Real.exp (-(l * s)) := by
  have hZ := Zf_pos a M ha h0 l
  have key := coeff_pow_of_scale a (tilt a M l) M (Real.exp l) (1 / Zf a M l)
    (fun i => by
      unfold tilt
      rw [mul_comm l, Real.exp_nat_mul]
      ring) m s
  rw [key, ← Real.exp_nat_mul, one_div, inv_pow]
  have e : Real.exp ((s : ℝ) * l) * Real.exp (-(l * s)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hZm : (Zf a M l ^ m)⁻¹ * Zf a M l ^ m = 1 := inv_mul_cancel₀ (pow_ne_zero _ hZ.ne')
  calc (gpoly a M ^ m).coeff s
      = (gpoly a M ^ m).coeff s * (Real.exp ((s : ℝ) * l) * Real.exp (-(l * s))) *
          ((Zf a M l ^ m)⁻¹ * Zf a M l ^ m) := by rw [e, hZm]; ring
    _ = _ := by ring

/-- The window bound (exponential tilting plus Chebyshev). -/
theorem window_bound (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (h0 : 0 < a 0) (l : ℝ) (m : ℕ)
    (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) :
    Real.exp (m * (Real.log (Zf a M l) - l * tmean a M l - δ * |l|)) *
        (1 - (M : ℝ) ^ 2 / (m * δ ^ 2)) ≤
      ∑ s ∈ (range (m * M + 1)).filter (fun s : ℕ => |(s : ℝ) - m * tmean a M l| < m * δ),
        (gpoly a M ^ m).coeff s := by
  set g := gpoly (tilt a M l) M with hg
  set μ := tmean a M l with hμ
  have hZ := Zf_pos a M ha h0 l
  have hg1 : g.eval 1 = 1 := eval_one_tilt a M ha h0 l
  have hgμ : (derivative g).eval 1 = μ := derivative_eval_one_tilt a M l
  have hg2 := second_moment_tilt_le a M ha h0 l
  rw [← hg, hgμ] at hg2
  have hn : (g ^ m).natDegree < m * M + 1 := natDegree_gpoly_pow_lt _ M m
  have hvar := sum_sq_dev g hg1 m (m * M + 1) hn
  rw [hgμ] at hvar
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hV : ∑ s ∈ range (m * M + 1), ((s : ℝ) - m * μ) ^ 2 * (g ^ m).coeff s ≤
      m * (M : ℝ) ^ 2 := by
    rw [hvar]
    have hsq := sq_nonneg μ
    have h3 : (derivative (derivative g)).eval 1 + μ - μ ^ 2 ≤ (M : ℝ) ^ 2 := by linarith
    exact mul_le_mul_of_nonneg_left h3 hmR.le
  have h1 : ∑ s ∈ range (m * M + 1), (g ^ m).coeff s = 1 := by
    rw [sum_coeff_eq_eval _ _ hn, eval_one_pow g hg1]
  have hcheb := sum_window_ge (g ^ m).coeff
    (coeff_gpoly_pow_nonneg _ (tilt_nonneg a M ha h0 l) M m) (m * M + 1) (m * μ) (m * δ)
    (m * (M : ℝ) ^ 2) (by positivity) h1 hV
  have hsimp : (m : ℝ) * (M : ℝ) ^ 2 / (m * δ) ^ 2 = (M : ℝ) ^ 2 / (m * δ ^ 2) := by
    field_simp
  rw [hsimp] at hcheb
  have hterm : ∀ s ∈ (range (m * M + 1)).filter (fun s : ℕ => |(s : ℝ) - m * μ| < m * δ),
      (g ^ m).coeff s * Real.exp (m * (Real.log (Zf a M l) - l * μ - δ * |l|)) ≤
        (gpoly a M ^ m).coeff s := by
    intro s hs
    rw [mem_filter] at hs
    rw [coeff_pow_tilt a M ha h0 l m s, ← hg, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (coeff_gpoly_pow_nonneg _ (tilt_nonneg a M ha h0 l) M m s)
    have hZm : Zf a M l ^ m = Real.exp (m * Real.log (Zf a M l)) := by
      rw [Real.exp_nat_mul, Real.exp_log hZ]
    rw [hZm, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl : l * ((s : ℝ) - m * μ) ≤ |l| * (m * δ) := by
      calc l * ((s : ℝ) - m * μ) ≤ |l * ((s : ℝ) - m * μ)| := le_abs_self _
        _ = |l| * |(s : ℝ) - m * μ| := abs_mul _ _
        _ ≤ |l| * (m * δ) := mul_le_mul_of_nonneg_left hs.2.le (abs_nonneg l)
    nlinarith
  calc Real.exp (m * (Real.log (Zf a M l) - l * μ - δ * |l|)) * (1 - (M : ℝ) ^ 2 / (m * δ ^ 2))
      ≤ Real.exp (m * (Real.log (Zf a M l) - l * μ - δ * |l|)) *
          ∑ s ∈ (range (m * M + 1)).filter (fun s : ℕ => |(s : ℝ) - m * μ| < m * δ),
            (g ^ m).coeff s :=
        mul_le_mul_of_nonneg_left hcheb (Real.exp_pos _).le
    _ = ∑ s ∈ (range (m * M + 1)).filter (fun s : ℕ => |(s : ℝ) - m * μ| < m * δ),
          (g ^ m).coeff s * Real.exp (m * (Real.log (Zf a M l) - l * μ - δ * |l|)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro s _
        ring
    _ ≤ ∑ s ∈ (range (m * M + 1)).filter (fun s : ℕ => |(s : ℝ) - m * μ| < m * δ),
          (gpoly a M ^ m).coeff s := sum_le_sum hterm

end P3L8
