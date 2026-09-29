import Research.Backfill.Paper3.Proof.CD.Pd

/-!
# The function `ψ_x(q) = log P_d(q) - x log q` and its minimisers

`ψ_x` is the paper's `φ` (`phiFun d γ = ψ_{2γd²}`). Its derivative at `1` is `d²/4 - x`, so
`ψ_x(q) < ψ_x(1)` for some `q > 1` when `x > d²/4` and for some `q < 1` when `x < d²/4`
(slopes). Minimisers exist over `[1, ∞)` when `x < d²` (`P_d(q) ≥ q^{d²}`) and over `(0, 1]` when
`x > 0` (`P_d ≥ 1`), by compactness; at an interior minimiser `q > 1` the tilted mean equals `x`
(Fermat).
-/

set_option autoImplicit false

namespace P3CD

open Finset Filter Topology BackfillPaper3.Challenge

/-- `ψ_x(q) = log P_d(q) - x log q`. -/
noncomputable def psi (d : ℕ) (x q : ℝ) : ℝ := Real.log (Pf d q) - x * Real.log q

theorem phiFun_eq_psi (d : ℕ) (γ q : ℝ) : phiFun d γ q = psi d (2 * γ * (d : ℝ) ^ 2) q := by
  unfold phiFun psi
  rw [evalR_Pd]

theorem psi_one (d : ℕ) (x : ℝ) : psi d x 1 = d * Real.log 4 := by
  unfold psi
  rw [Pf_one, Real.log_one, mul_zero, sub_zero, Real.log_pow]

theorem psi_one_nonneg (d : ℕ) (x : ℝ) : 0 ≤ psi d x 1 := by
  rw [psi_one]
  have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  positivity

theorem hasDerivAt_psi (d : ℕ) (x : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (psi d x) (dPf d q / Pf d q - x / q) q := by
  have h1 := (hasDerivAt_Pf d q).log (Pf_pos d hq.le).ne'
  have h2 := (Real.hasDerivAt_log hq.ne').const_mul x
  have h := h1.sub h2
  rw [show x * q⁻¹ = x / q from (div_eq_mul_inv x q).symm] at h
  exact h

theorem hasDerivAt_psi_one (d : ℕ) (hd : 1 ≤ d) (x : ℝ) :
    HasDerivAt (psi d x) ((d : ℝ) ^ 2 / 4 - x) 1 := by
  have h := hasDerivAt_psi d x one_pos
  rwa [dPf_div_Pf_one d hd, div_one] at h

theorem exists_gt_one_psi_lt (d : ℕ) (hd : 1 ≤ d) {x : ℝ} (hx : (d : ℝ) ^ 2 / 4 < x) :
    ∃ q, 1 < q ∧ psi d x q < psi d x 1 := by
  have ht := (hasDerivAt_psi_one d hd x).tendsto_slope
  have hneg : (d : ℝ) ^ 2 / 4 - x < 0 := by linarith
  have h1 : ∀ᶠ q in 𝓝[>] (1 : ℝ), slope (psi d x) 1 q < 0 :=
    (ht.mono_left (nhdsWithin_mono _ fun y (hy : 1 < y) =>
      Set.mem_compl_singleton_iff.2 (ne_of_gt hy))).eventually (gt_mem_nhds hneg)
  obtain ⟨q, hq, hq1⟩ := (h1.and self_mem_nhdsWithin).exists
  have hq1' : (1 : ℝ) < q := hq1
  refine ⟨q, hq1', ?_⟩
  rw [slope_def_field] at hq
  by_contra hcon
  rw [not_lt] at hcon
  have : 0 ≤ (psi d x q - psi d x 1) / (q - 1) := div_nonneg (by linarith) (by linarith)
  linarith

theorem exists_lt_one_psi_lt (d : ℕ) (hd : 1 ≤ d) {x : ℝ} (hx : x < (d : ℝ) ^ 2 / 4) :
    ∃ q, 0 < q ∧ q < 1 ∧ psi d x q < psi d x 1 := by
  have ht := (hasDerivAt_psi_one d hd x).tendsto_slope
  have hpos : 0 < (d : ℝ) ^ 2 / 4 - x := by linarith
  have h1 : ∀ᶠ q in 𝓝[<] (1 : ℝ), 0 < slope (psi d x) 1 q :=
    (ht.mono_left (nhdsWithin_mono _ fun y (hy : y < 1) =>
      Set.mem_compl_singleton_iff.2 (ne_of_lt hy))).eventually (lt_mem_nhds hpos)
  have h2 : ∀ᶠ q in 𝓝[<] (1 : ℝ), 0 < q := nhdsWithin_le_nhds (lt_mem_nhds one_pos)
  obtain ⟨q, ⟨hq, hq0⟩, hq1⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  have hq1' : q < 1 := hq1
  refine ⟨q, hq0, hq1', ?_⟩
  rw [slope_def_field] at hq
  by_contra hcon
  rw [not_lt] at hcon
  have : (psi d x q - psi d x 1) / (q - 1) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith)
    (by linarith)
  linarith

theorem continuousOn_psi (d : ℕ) (x : ℝ) : ContinuousOn (psi d x) (Set.Ioi 0) := by
  unfold psi
  apply ContinuousOn.sub
  · exact ContinuousOn.log (continuous_Pf d).continuousOn fun q hq =>
      (Pf_pos d (le_of_lt hq)).ne'
  · exact continuousOn_const.mul (Real.continuousOn_log.mono fun q (hq : 0 < q) =>
      Set.mem_compl_singleton_iff.2 (ne_of_gt hq))

theorem psi_ge_of_one_le (d : ℕ) (x : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    ((d : ℝ) ^ 2 - x) * Real.log q ≤ psi d x q := by
  unfold psi
  have h1 : Real.log (q ^ (d ^ 2)) ≤ Real.log (Pf d q) :=
    Real.log_le_log (by positivity) (pow_le_Pf d (by linarith))
  rw [Real.log_pow] at h1
  push_cast at h1
  have e : ((d : ℝ) ^ 2 - x) * Real.log q = (d : ℝ) ^ 2 * Real.log q - x * Real.log q := by ring
  linarith

theorem psi_ge_of_pos (d : ℕ) (x : ℝ) {q : ℝ} (hq0 : 0 < q) : -x * Real.log q ≤ psi d x q := by
  unfold psi
  have : 0 ≤ Real.log (Pf d q) := Real.log_nonneg (one_le_Pf d hq0.le)
  linarith

/-- A minimiser of `ψ_x` over `[1, ∞)` exists when `x < d²`. -/
theorem exists_min_ge_one (d : ℕ) {x : ℝ} (hx : x < (d : ℝ) ^ 2) :
    ∃ q, 1 ≤ q ∧ ∀ q', 1 ≤ q' → psi d x q ≤ psi d x q' := by
  set c := (d : ℝ) ^ 2 - x with hc
  have hc0 : 0 < c := by linarith
  set Q := Real.exp (psi d x 1 / c + 1) with hQ
  have hQ1 : 1 ≤ Q := Real.one_le_exp (by have := psi_one_nonneg d x; positivity)
  obtain ⟨q, hqI, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hQ1)
    ((continuousOn_psi d x).mono fun y hy => lt_of_lt_of_le one_pos hy.1)
  refine ⟨q, hqI.1, fun q' hq' => ?_⟩
  by_cases hq'Q : q' ≤ Q
  · exact isMinOn_iff.1 hmin q' ⟨hq', hq'Q⟩
  · rw [not_le] at hq'Q
    have h1 : psi d x q ≤ psi d x 1 := isMinOn_iff.1 hmin 1 ⟨le_rfl, hQ1⟩
    have h2 : c * Real.log Q < c * Real.log q' :=
      mul_lt_mul_of_pos_left (Real.log_lt_log (by positivity) hq'Q) hc0
    have h3 : c * Real.log q' ≤ psi d x q' := psi_ge_of_one_le d x hq'
    have h4 : c * Real.log Q = psi d x 1 + c := by
      rw [hQ, Real.log_exp]
      field_simp
    linarith

/-- A minimiser of `ψ_x` over `(0, 1]` exists when `x > 0`. -/
theorem exists_min_le_one (d : ℕ) {x : ℝ} (hx : 0 < x) :
    ∃ q, 0 < q ∧ q ≤ 1 ∧ ∀ q', 0 < q' → q' ≤ 1 → psi d x q ≤ psi d x q' := by
  set δ := Real.exp (-(psi d x 1 / x) - 1) with hδ
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ psi d x 1 / x := div_nonneg (psi_one_nonneg d x) hx.le
    linarith)
  obtain ⟨q, hqI, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hδ1)
    ((continuousOn_psi d x).mono fun y hy => lt_of_lt_of_le hδ0 hy.1)
  refine ⟨q, lt_of_lt_of_le hδ0 hqI.1, hqI.2, fun q' hq'0 hq'1 => ?_⟩
  by_cases hq'δ : δ ≤ q'
  · exact isMinOn_iff.1 hmin q' ⟨hq'δ, hq'1⟩
  · rw [not_le] at hq'δ
    have h1 : psi d x q ≤ psi d x 1 := isMinOn_iff.1 hmin 1 ⟨hδ1, le_rfl⟩
    have h2 : x * Real.log q' < x * Real.log δ :=
      mul_lt_mul_of_pos_left (Real.log_lt_log hq'0 hq'δ) hx
    have h3 : -x * Real.log q' ≤ psi d x q' := psi_ge_of_pos d x hq'0
    have h4 : x * Real.log δ = -(psi d x 1) - x := by
      rw [hδ, Real.log_exp]
      field_simp
    linarith

/-- For `d²/4 < x < d²`, `ψ_x` has a minimiser `q* > 1` over `[1, ∞)`. -/
theorem exists_qstar_gt (d : ℕ) (hd : 1 ≤ d) {x : ℝ} (hx1 : (d : ℝ) ^ 2 / 4 < x)
    (hx2 : x < (d : ℝ) ^ 2) : ∃ q, 1 < q ∧ ∀ q', 1 ≤ q' → psi d x q ≤ psi d x q' := by
  obtain ⟨q, hq1, hmin⟩ := exists_min_ge_one d hx2
  obtain ⟨q₀, hq₀, hlt⟩ := exists_gt_one_psi_lt d hd hx1
  refine ⟨q, lt_of_le_of_ne hq1 ?_, hmin⟩
  rintro rfl
  exact absurd (hmin q₀ hq₀.le) (not_le.2 hlt)

/-- For `0 < x < d²/4`, `ψ_x` has a minimiser `q* < 1` over `(0, 1]`. -/
theorem exists_qstar_lt (d : ℕ) (hd : 1 ≤ d) {x : ℝ} (hx0 : 0 < x) (hx1 : x < (d : ℝ) ^ 2 / 4) :
    ∃ q, 0 < q ∧ q < 1 ∧ ∀ q', 0 < q' → q' ≤ 1 → psi d x q ≤ psi d x q' := by
  obtain ⟨q, hq0, hq1, hmin⟩ := exists_min_le_one d hx0
  obtain ⟨q₀, hq₀0, hq₀1, hlt⟩ := exists_lt_one_psi_lt d hd hx1
  refine ⟨q, hq0, lt_of_le_of_ne hq1 ?_, hmin⟩
  rintro rfl
  exact absurd (hmin q₀ hq₀0 hq₀1.le) (not_le.2 hlt)

/-- When `x > d²/4`, a minimiser of `ψ_x` over `[1, ∞)` is not `1`. -/
theorem one_lt_of_min (d : ℕ) (hd : 1 ≤ d) {x q : ℝ} (hx : (d : ℝ) ^ 2 / 4 < x) (hq : 1 ≤ q)
    (hmin : ∀ q', 1 ≤ q' → psi d x q ≤ psi d x q') : 1 < q := by
  obtain ⟨q₀, hq₀, hlt⟩ := exists_gt_one_psi_lt d hd hx
  refine lt_of_le_of_ne hq ?_
  rintro rfl
  exact absurd (hmin q₀ hq₀.le) (not_le.2 hlt)

/-- Fermat: at a minimiser `q > 1` over `[1, ∞)`, `P_d'(q)/P_d(q) = x/q`. -/
theorem deriv_eq_of_min (d : ℕ) {x q : ℝ} (hq : 1 < q)
    (hmin : ∀ q', 1 ≤ q' → psi d x q ≤ psi d x q') : dPf d q / Pf d q = x / q := by
  have hloc : IsLocalMin (psi d x) q :=
    (lt_mem_nhds hq).mono fun y hy => hmin y hy.le
  have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_psi d x (by linarith))
  linarith

/-- At a minimiser `q > 1` over `[1, ∞)`, the tilted mean equals `x`. -/
theorem tmean_eq_of_min (d : ℕ) {x q : ℝ} (hq : 1 < q)
    (hmin : ∀ q', 1 ≤ q' → psi d x q ≤ psi d x q') : tmean d q = x := by
  have h := deriv_eq_of_min d hq hmin
  unfold tmean
  rw [mul_div_assoc, h]
  field_simp

end P3CD
