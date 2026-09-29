import Research.Backfill.Paper3.Proof.CD.Psi
import Research.Backfill.Paper3.Proof.CD.Gn

/-!
# Remark 10(c) — the minimiser `q*` and the base `P_d(q*)² / P_H(q*)`

(1) For `1/8 < γ < 1/2` a minimiser `q* > 1` of `φ = ψ_{2γd²}` over `[1, ∞)` exists.
(2) The base tends to `1` as `γ ↓ 1/8`, uniformly over minimisers: the base is continuous at
`q = 1` with value `1`; at a minimiser `q > 1` Fermat gives `μ(q) = 2γd²` for the tilted mean
`μ`, which is monotone with `μ(1 + η) > μ(1) = d²/4`, so `q < 1 + η` once `2γd² < μ(1 + η)`.
(3) For `d = 2`: `P_2(q) = 7 + 4q + 4q² + q⁴`, `D = (q - 1)³`, `P_{H_2} = P_2² - 2(q - 1)⁴`
(Lemma 6); the minimiser satisfies `q⁴ = 2q + 7` (`γ = 1/4`) resp. `q⁴ = 96q² + 146q + 343`
(`γ = 49/100`), which puts it in `(9/5, 181/100)` resp. `(53/5, 1063/100)`; monotone bounds on
these intervals give the stated enclosures of the base.
-/

set_option autoImplicit false

namespace P3CD

open Finset Filter Topology SimpleGraph Polynomial BackfillPaper3.Challenge P3Basic

theorem isQStar_iff (d : ℕ) (γ q : ℝ) :
    IsQStar d γ q ↔ 1 ≤ q ∧ ∀ q', 1 ≤ q' →
      psi d (2 * γ * (d : ℝ) ^ 2) q ≤ psi d (2 * γ * (d : ℝ) ^ 2) q' := by
  unfold IsQStar
  simp only [phiFun_eq_psi]

/-- Remark 10(c), existence of `q* > 1`. -/
theorem remark10c_exists (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ1 : 1 / 8 < γ) (hγ2 : γ < 1 / 2) :
    ∃ q : ℝ, 1 < q ∧ IsQStar d γ q := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  obtain ⟨q, hq1, hmin⟩ := exists_qstar_gt d hd1 (x := 2 * γ * (d : ℝ) ^ 2) (by nlinarith)
    (by nlinarith)
  exact ⟨q, hq1, (isQStar_iff d γ q).2 ⟨hq1.le, hmin⟩⟩

theorem continuous_evalR_edgePoly {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Continuous fun q : ℝ => evalR (edgePoly G) q := by
  simp only [evalR_edgePoly]
  exact continuous_finsetSum _ fun A _ => continuous_pow _

theorem baseRatio_one (d : ℕ) (a₁ b₁ a₂ b₂ : Fin d) : baseRatio d a₁ b₁ a₂ b₂ 1 = 1 := by
  unfold baseRatio
  rw [evalR_Pd, Pf_one, evalR_edgePoly_one]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum]
  rw [div_eq_one_iff_eq (by positivity), ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  congr 1
  ring

/-- Remark 10(c), the limit `γ ↓ 1/8`. -/
theorem remark10c_limit (d : ℕ) (hd : 2 ≤ d) (a₁ b₁ a₂ b₂ : Fin d) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ q : ℝ, 1 / 8 < γ → γ < 1 / 8 + δ → IsQStar d γ q →
      |baseRatio d a₁ b₁ a₂ b₂ q - 1| < ε := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hcont : ContinuousAt (baseRatio d a₁ b₁ a₂ b₂) 1 := by
    have h1 : ContinuousAt (fun q : ℝ => evalR (Pd d) q ^ 2) 1 := by
      simp only [evalR_Pd]
      exact ((continuous_Pf d).pow 2).continuousAt
    have h2 : ContinuousAt (fun q : ℝ => evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q) 1 :=
      (continuous_evalR_edgePoly _).continuousAt
    have h3 : evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) 1 ≠ 0 := by
      rw [evalR_edgePoly_one]
      positivity
    exact h1.div h2 h3
  obtain ⟨η, hη, hηε⟩ := Metric.continuousAt_iff.1 hcont ε hε
  have hκ : (d : ℝ) ^ 2 / 4 < tmean d (1 + η / 2) := by
    rw [← tmean_one d hd1]
    exact tmean_strict d hd1 one_pos (by linarith)
  refine ⟨(tmean d (1 + η / 2) - (d : ℝ) ^ 2 / 4) / (2 * (d : ℝ) ^ 2), by
    apply div_pos (by linarith) (by positivity), fun γ q hγ1 hγ2 hq => ?_⟩
  obtain ⟨hq1, hmin⟩ := (isQStar_iff d γ q).1 hq
  rcases eq_or_lt_of_le hq1 with rfl | hq1'
  · rw [baseRatio_one, sub_self, abs_zero]
    exact hε
  · have hμ := tmean_eq_of_min d hq1' hmin
    have hx : 2 * γ * (d : ℝ) ^ 2 < tmean d (1 + η / 2) := by
      have h := mul_lt_mul_of_pos_left hγ2 (by positivity : (0 : ℝ) < 2 * (d : ℝ) ^ 2)
      have e : 2 * (d : ℝ) ^ 2 * (1 / 8 + (tmean d (1 + η / 2) - (d : ℝ) ^ 2 / 4) /
          (2 * (d : ℝ) ^ 2)) = tmean d (1 + η / 2) := by
        field_simp
        ring
      nlinarith
    have hqη : q < 1 + η / 2 := by
      by_contra hcon
      rw [not_lt] at hcon
      have := tmean_mono d (by linarith) hcon
      linarith
    have hdist : dist q 1 < η := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have := hηε hdist
    rwa [baseRatio_one, Real.dist_eq] at this

/-! ### `d = 2` -/

theorem Pf_two (q : ℝ) : Pf 2 q = 7 + 4 * q + 4 * q ^ 2 + q ^ 4 := by
  simp [Pf, wt, Finset.sum_range_succ]
  ring

theorem dPf_two (q : ℝ) : dPf 2 q = 4 + 8 * q + 4 * q ^ 3 := by
  simp [dPf, wt, Finset.sum_range_succ]
  ring

theorem evalR_Dpoly_two (q : ℝ) : evalR (Dpoly 2) q = (q - 1) ^ 3 := by
  simp [evalR, Dpoly, Wpoly, Finset.sum_range_succ]
  ring

theorem evalR_H2 (h6 : Lemma6) (q : ℝ) :
    evalR (edgePoly (Hd 2 0 0 0 0)) q = Pf 2 q ^ 2 - 2 * (q - 1) ^ 4 := by
  have h := base_diff h6 2 le_rfl 0 0 0 0 q
  rw [evalR_Dpoly_two] at h
  have e : 2 * (q - 1) * (q - 1) ^ 3 = 2 * (q - 1) ^ 4 := by ring
  linarith

theorem baseRatio_two (h6 : Lemma6) (q : ℝ) :
    baseRatio 2 0 0 0 0 q = Pf 2 q ^ 2 / (Pf 2 q ^ 2 - 2 * (q - 1) ^ 4) := by
  unfold baseRatio
  rw [evalR_Pd, evalR_H2 h6]

/-- A minimiser for `d = 2`, `γ > 1/8` satisfies `q P_2'(q) = x P_2(q)` with `q > 1`. -/
theorem qstar_two (γ q : ℝ) (hγ : 1 / 8 < γ) (hq : IsQStar 2 γ q) :
    1 < q ∧ q * (4 + 8 * q + 4 * q ^ 3) = 8 * γ * (7 + 4 * q + 4 * q ^ 2 + q ^ 4) := by
  obtain ⟨hq1, hmin⟩ := (isQStar_iff 2 γ q).1 hq
  have hx : ((2 : ℕ) : ℝ) ^ 2 / 4 < 2 * γ * ((2 : ℕ) : ℝ) ^ 2 := by push_cast; nlinarith
  have hq1' := one_lt_of_min 2 (by norm_num) hx hq1 hmin
  refine ⟨hq1', ?_⟩
  have hq0 : 0 < q := by linarith
  have h := deriv_eq_of_min 2 hq1' hmin
  rw [dPf_two, Pf_two, div_eq_div_iff (by positivity) hq0.ne'] at h
  push_cast at h
  nlinarith

theorem remark10c_quarter (h6 : Lemma6) (q : ℝ) (hq : IsQStar 2 (1 / 4) q) :
    (100055 / 100000 : ℝ) ≤ baseRatio 2 0 0 0 0 q ∧
      baseRatio 2 0 0 0 0 q < 100065 / 100000 := by
  obtain ⟨hq1, heq⟩ := qstar_two (1 / 4) q (by norm_num) hq
  have hq0 : 0 < q := by linarith
  -- `q⁴ = 2q + 7`
  have hlo : 9 / 5 < q := by
    by_contra h
    rw [not_lt] at h
    have h3 : q ^ 3 ≤ (9 / 5) ^ 3 := pow_le_pow_left₀ hq0.le h 3
    nlinarith [mul_le_mul_of_nonneg_left h3 hq0.le]
  have hhi : q < 181 / 100 := by
    by_contra h
    rw [not_lt] at h
    have h3 : (181 / 100) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
    nlinarith [mul_le_mul_of_nonneg_left h3 hq0.le]
  have hP1 : Pf 2 (9 / 5) ≤ Pf 2 q := Pf_mono 2 (by norm_num) hlo.le
  have hP2 : Pf 2 q ≤ Pf 2 (181 / 100) := Pf_mono 2 hq0.le hhi.le
  rw [Pf_two (9 / 5)] at hP1
  rw [Pf_two (181 / 100)] at hP2
  norm_num at hP1 hP2
  have hPpos : 0 < Pf 2 q := Pf_pos 2 hq0.le
  have hPsq1 := pow_le_pow_left₀ (by norm_num) hP1 2
  have hPsq2 := pow_le_pow_left₀ hPpos.le hP2 2
  have hu1 : (4 / 5 : ℝ) ^ 4 ≤ (q - 1) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hu2 : (q - 1) ^ 4 ≤ (81 / 100 : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  norm_num at hPsq1 hPsq2 hu1 hu2
  have hden : 0 < Pf 2 q ^ 2 - 2 * (q - 1) ^ 4 := by linarith
  rw [baseRatio_two h6]
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_lt_iff₀ hden]
    linarith

theorem remark10c_049 (h6 : Lemma6) (q : ℝ) (hq : IsQStar 2 (49 / 100) q) :
    (100005 / 100000 : ℝ) ≤ baseRatio 2 0 0 0 0 q ∧
      baseRatio 2 0 0 0 0 q < 100015 / 100000 := by
  obtain ⟨hq1, heq⟩ := qstar_two (49 / 100) q (by norm_num) hq
  have hq0 : 0 < q := by linarith
  -- `q⁴ = 96 q² + 146 q + 343`
  have hlo : 53 / 5 < q := by
    by_contra h
    rw [not_lt] at h
    have h2 : q ^ 2 ≤ (53 / 5) ^ 2 := pow_le_pow_left₀ hq0.le h 2
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg q), mul_le_mul_of_nonneg_left h hq0.le]
  have hhi : q < 1063 / 100 := by
    by_contra h
    rw [not_lt] at h
    have h2 : (1063 / 100) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg q), mul_le_mul_of_nonneg_left h hq0.le]
  have hP1 : Pf 2 (53 / 5) ≤ Pf 2 q := Pf_mono 2 (by norm_num) hlo.le
  have hP2 : Pf 2 q ≤ Pf 2 (1063 / 100) := Pf_mono 2 hq0.le hhi.le
  rw [Pf_two (53 / 5)] at hP1
  rw [Pf_two (1063 / 100)] at hP2
  norm_num at hP1 hP2
  have hPpos : 0 < Pf 2 q := Pf_pos 2 hq0.le
  have hPsq1 := pow_le_pow_left₀ (by norm_num) hP1 2
  have hPsq2 := pow_le_pow_left₀ hPpos.le hP2 2
  have hu1 : (48 / 5 : ℝ) ^ 4 ≤ (q - 1) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hu2 : (q - 1) ^ 4 ≤ (963 / 100 : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  norm_num at hPsq1 hPsq2 hu1 hu2
  have hden : 0 < Pf 2 q ^ 2 - 2 * (q - 1) ^ 4 := by linarith
  rw [baseRatio_two h6]
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_lt_iff₀ hden]
    linarith

theorem remark10c (h6 : Lemma6) : Remark10c :=
  ⟨fun d hd γ hγ1 hγ2 => remark10c_exists d hd γ hγ1 hγ2,
    fun d hd a₁ b₁ a₂ b₂ ε hε => remark10c_limit d hd a₁ b₁ a₂ b₂ ε hε,
    fun q hq => remark10c_quarter h6 q hq,
    fun q hq => remark10c_049 h6 q hq⟩

end P3CD
