import Research.Backfill.Paper3.Proof.CD.Law
import Research.Backfill.Paper3.Proof.CD.Psi

/-!
# `ρ(d, γ)`, Remark 9 and Proposition C

`rhoFun ≥ 0` on `(0, 1]` (so the infimum `ρ` is a true infimum, `Rho_bddBelow`); Remark 9 by the
substitution `q = e^{-t/d}`; Proposition C: the upper bound from `SSSZBound` and the Markov
bound; the limit for `m K_{d,d}`: the upper half from the Markov bound with `P_{mK} = P_d^m`,
the lower half by cases: `γ = 0` exactly (`i_0(mK) = P_d(0)^m` and continuity of `P_d` at `0`),
`0 < γ < 1/8` from Lemma 8(b) at `x = 2γd²`, and `γ ≥ 1/8` from Lemma 8(b) at `x' < d²/4` with
the Jensen bound (this replaces the central limit theorem used in the paper).
-/

set_option autoImplicit false

namespace P3CD

open Finset Filter Topology BackfillPaper3.Challenge P3Basic

theorem rhoFun_eq (d : ℕ) (γ q : ℝ) :
    rhoFun d γ q = 1 / (2 * (d : ℝ)) * Real.log (Pf d q) - γ * d * Real.log q := by
  unfold rhoFun
  rw [evalR_Pd]

theorem rhoFun_nonneg (d : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ rhoFun d γ q := by
  rw [rhoFun_eq]
  have h1 : 0 ≤ 1 / (2 * (d : ℝ)) * Real.log (Pf d q) :=
    mul_nonneg (by positivity) (Real.log_nonneg (one_le_Pf d hq0.le))
  have h2 : γ * d * Real.log q ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (Real.log_nonpos hq0.le hq1)
  linarith

theorem rho_bddBelow : Rho_bddBelow := by
  intro d _ γ hγ
  refine ⟨0, ?_⟩
  rintro _ ⟨⟨q, hq0, hq1⟩, rfl⟩
  exact rhoFun_nonneg d hγ hq0 hq1

theorem rho_le_rhoFun (d : ℕ) (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 ≤ γ) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q ≤ 1) : rho d γ ≤ rhoFun d γ q :=
  ciInf_le (rho_bddBelow d hd γ hγ) (⟨q, hq0, hq1⟩ : Set.Ioc (0 : ℝ) 1)

theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

theorem rhoFun_one (d : ℕ) (hd : 1 ≤ d) (γ : ℝ) : rhoFun d γ 1 = Real.log 2 := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  rw [rhoFun_eq, Pf_one, Real.log_one, mul_zero, sub_zero, Real.log_pow, log_four]
  field_simp

theorem rho_le_log_two (d : ℕ) (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 ≤ γ) : rho d γ ≤ Real.log 2 :=
  (rho_le_rhoFun d hd hγ one_pos le_rfl).trans_eq (rhoFun_one d hd γ)

instance : Nonempty (Set.Ioc (0 : ℝ) 1) := ⟨⟨1, one_pos, le_rfl⟩⟩

/-! ### Remark 9 -/

theorem remark9 : Remark9 := by
  intro d hd γ hγ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have key : ∀ t : ℝ, γ * t + 1 / (2 * (d : ℝ)) * Real.log (evalR (Pd d) (Real.exp (-t / d))) =
      rhoFun d γ (Real.exp (-t / d)) := by
    intro t
    rw [rhoFun_eq, evalR_Pd, Real.log_exp]
    field_simp
    ring
  have hq1 : ∀ t : ℝ, 0 ≤ t → Real.exp (-t / d) ≤ 1 := fun t ht =>
    Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hd0.le)
  have hbdd : BddBelow (Set.range fun t : Set.Ici (0 : ℝ) =>
      γ * t + 1 / (2 * (d : ℝ)) * Real.log (evalR (Pd d) (Real.exp (-t / d)))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨⟨t, ht⟩, rfl⟩
    dsimp only
    rw [key]
    exact rhoFun_nonneg d hγ (Real.exp_pos _) (hq1 t ht)
  apply le_antisymm
  · apply le_ciInf
    rintro ⟨t, ht⟩
    rw [key]
    exact rho_le_rhoFun d hd hγ (Real.exp_pos _) (hq1 t ht)
  · unfold rho
    apply le_ciInf
    rintro ⟨q, hq0, hq1'⟩
    have ht : (0 : ℝ) ≤ -(d * Real.log q) := by
      have := Real.log_nonpos hq0.le hq1'
      nlinarith
    calc (⨅ t : Set.Ici (0 : ℝ),
          γ * t + 1 / (2 * (d : ℝ)) * Real.log (evalR (Pd d) (Real.exp (-t / d))))
        ≤ γ * (-(d * Real.log q)) + 1 / (2 * (d : ℝ)) *
            Real.log (evalR (Pd d) (Real.exp (-(-(d * Real.log q)) / d))) :=
          ciInf_le hbdd (⟨-(d * Real.log q), ht⟩ : Set.Ici (0 : ℝ))
      _ = rhoFun d γ q := by
          rw [key]
          congr 1
          rw [neg_neg, mul_div_cancel_left₀ _ hd0.ne', Real.exp_log hq0]

/-! ### Proposition C, upper bound -/

theorem propC_upper (hS : SSSZBound) (d : ℕ) (hd : 2 ≤ d) {γ : ℝ} (hγ : 0 ≤ γ)
    (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 0 < Fintype.card V) (hG : G.IsRegularOfDegree d) :
    1 / (Fintype.card V : ℝ) * Real.log (iGamma G d γ) ≤ rho d γ := by
  unfold rho
  apply le_ciInf
  rintro ⟨q, hq0, hq1⟩
  set n := Fintype.card V
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hP := Pf_pos d hq0.le
  have h1 : (iGamma G d γ : ℝ) ≤ q ^ (-(γ * d * n)) * evalR (edgePoly G) q := by
    rw [iGamma_eq_card]
    exact card_le_markov G _ hq0 hq1
  have h2 : evalR (edgePoly G) q ≤ Pf d q ^ ((n : ℝ) / (2 * d)) := by
    rw [← evalR_Pd]
    exact hS d (by omega) V G hG q hq0 hq1
  have hi : (0 : ℝ) < iGamma G d γ := by exact_mod_cast one_le_iGamma G d hγ
  have h3 : Real.log (iGamma G d γ) ≤
      -(γ * d * n) * Real.log q + (n / (2 * d)) * Real.log (Pf d q) := by
    have h4 : (iGamma G d γ : ℝ) ≤ q ^ (-(γ * d * n)) * Pf d q ^ ((n : ℝ) / (2 * d)) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    have := Real.log_le_log hi h4
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_rpow hq0,
      Real.log_rpow hP] at this
  show 1 / (n : ℝ) * Real.log (iGamma G d γ) ≤ rhoFun d γ q
  rw [rhoFun_eq]
  calc 1 / (n : ℝ) * Real.log (iGamma G d γ)
      ≤ 1 / n * (-(γ * d * n) * Real.log q + (n / (2 * d)) * Real.log (Pf d q)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by
        field_simp
        ring

/-! ### Proposition C, the limit -/

/-- `i_0(m K_{d,d}) = P_d(0)^m`. -/
theorem iGamma_zero_KddUnion (m d : ℕ) : (iGamma (KddUnion m d) d 0 : ℝ) = Pf d 0 ^ m := by
  rw [← evalR_KddUnion, evalR_edgePoly, iGamma_eq_card, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases h : edgesIn (KddUnion m d) A = 0
  · simp [h]
  · have hpos : (0 : ℝ) < edgesIn (KddUnion m d) A := by exact_mod_cast Nat.pos_of_ne_zero h
    rw [zero_pow h]
    simp [not_le.2 hpos]

theorem rho_zero_le (d : ℕ) (hd : 1 ≤ d) : rho d 0 ≤ 1 / (2 * (d : ℝ)) * Real.log (Pf d 0) := by
  have hc : ContinuousAt (fun q => 1 / (2 * (d : ℝ)) * Real.log (Pf d q)) 0 :=
    continuousAt_const.mul ((continuous_Pf d).continuousAt.log (Pf_pos d le_rfl).ne')
  have ht : Tendsto (fun q => 1 / (2 * (d : ℝ)) * Real.log (Pf d q)) (𝓝[>] 0)
      (𝓝 (1 / (2 * (d : ℝ)) * Real.log (Pf d 0))) := hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with q hq
  have := rho_le_rhoFun d hd le_rfl hq.1 hq.2.le
  rw [rhoFun_eq] at this
  simpa using this

/-- From `e^{mL} ≤ i` with `m ≥ 1`: `L/(2d) ≤ (1/(2dm)) log i`. -/
theorem div_le_of_exp_le {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) {L i : ℝ}
    (h : Real.exp (m * L) ≤ i) : L / (2 * d) ≤ 1 / ((2 * d * m : ℕ) : ℝ) * Real.log i := by
  have hi : 0 < i := lt_of_lt_of_le (Real.exp_pos _) h
  have h1 : m * L ≤ Real.log i := by
    rw [← Real.log_exp (m * L)]
    exact Real.log_le_log (Real.exp_pos _) h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  push_cast
  rw [div_le_iff₀ (by positivity)]
  calc L = (m * L) / m := by field_simp
    _ ≤ Real.log i / m := div_le_div_of_nonneg_right h1 hmR.le
    _ = 1 / (2 * d * m) * Real.log i * (2 * d) := by field_simp

/-- The Jensen bound in the form used for `γ ≥ 1/8`: for `q > 0` and `t ∈ [0, 1]`,
`log P_d(q) - (d²/4)(1 - t) log q ≥ d log 4 - a t` with `a = d log 4 - log P_d(0)`. -/
theorem jensen_lower (d : ℕ) (hd : 1 ≤ d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {q : ℝ}
    (hq0 : 0 < q) :
    d * Real.log 4 - (d * Real.log 4 - Real.log (Pf d 0)) * t ≤
      Real.log (Pf d q) - (d : ℝ) ^ 2 / 4 * (1 - t) * Real.log q := by
  have hA : d * Real.log 4 + (d : ℝ) ^ 2 / 4 * Real.log q ≤ Real.log (Pf d q) := by
    have h := Pf_ge_jensen d hd hq0
    have h' := Real.log_le_log (by positivity) h
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_rpow hq0] at h'
  have hB : Real.log (Pf d 0) ≤ Real.log (Pf d q) :=
    Real.log_le_log (Pf_pos d le_rfl) (Pf_mono d le_rfl hq0.le)
  set a := d * Real.log 4 - Real.log (Pf d 0) with ha
  set μ := (d : ℝ) ^ 2 / 4 with hμ
  rcases le_total (-(μ * Real.log q)) a with h | h
  · have : -(μ * Real.log q) * t ≤ a * t := mul_le_mul_of_nonneg_right h ht0
    nlinarith
  · have : a * (1 - t) ≤ -(μ * Real.log q) * (1 - t) := mul_le_mul_of_nonneg_right h (by linarith)
    nlinarith

theorem propC_limit (h8 : Lemma8) (d : ℕ) (hd : 2 ≤ d) {γ : ℝ} (hγ : 0 ≤ γ) :
    Tendsto (fun m : ℕ => 1 / ((2 * d * m : ℕ) : ℝ) * Real.log (iGamma (KddUnion m d) d γ))
      atTop (𝓝 (rho d γ)) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hcard : ∀ m : ℕ, (Fintype.card (Fin m × (Fin d ⊕ Fin d)) : ℝ) = 2 * d * m := by
    intro m
    rw [card_KddUnion]
    push_cast
    ring
  -- upper half
  have hup : ∀ m : ℕ, 1 ≤ m →
      1 / ((2 * d * m : ℕ) : ℝ) * Real.log (iGamma (KddUnion m d) d γ) ≤ rho d γ := by
    intro m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    unfold rho
    apply le_ciInf
    rintro ⟨q, hq0, hq1⟩
    have hP := Pf_pos d hq0.le
    have h1 : (iGamma (KddUnion m d) d γ : ℝ) ≤
        q ^ (-(γ * d * (2 * d * m))) * Pf d q ^ m := by
      rw [iGamma_eq_card, ← evalR_KddUnion, ← hcard]
      exact card_le_markov _ _ hq0 hq1
    have hi : (0 : ℝ) < iGamma (KddUnion m d) d γ := by
      exact_mod_cast one_le_iGamma (KddUnion m d) d hγ
    have h3 : Real.log (iGamma (KddUnion m d) d γ) ≤
        -(γ * d * (2 * d * m)) * Real.log q + m * Real.log (Pf d q) := by
      have := Real.log_le_log hi h1
      rwa [Real.log_mul (by positivity) (by positivity), Real.log_rpow hq0,
        Real.log_pow] at this
    show _ ≤ rhoFun d γ q
    rw [rhoFun_eq]
    push_cast
    calc 1 / (2 * (d : ℝ) * m) * Real.log (iGamma (KddUnion m d) d γ)
        ≤ 1 / (2 * d * m) * (-(γ * d * (2 * d * m)) * Real.log q + m * Real.log (Pf d q)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by
          field_simp
          ring
  -- lower half
  have hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      rho d γ - ε ≤ 1 / ((2 * d * m : ℕ) : ℝ) * Real.log (iGamma (KddUnion m d) d γ) := by
    intro ε hε
    rcases eq_or_lt_of_le hγ with h0 | hγpos
    · -- γ = 0
      subst h0
      filter_upwards [eventually_ge_atTop 1] with m hm
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      rw [iGamma_zero_KddUnion, Real.log_pow]
      have e : 1 / ((2 * d * m : ℕ) : ℝ) * (m * Real.log (Pf d 0)) =
          1 / (2 * (d : ℝ)) * Real.log (Pf d 0) := by
        push_cast
        field_simp
      rw [e]
      linarith [rho_zero_le d hd1]
    rcases lt_or_ge γ (1 / 8) with hγ8 | hγ8
    · -- 0 < γ < 1/8
      have hx0 : 0 < 2 * γ * (d : ℝ) ^ 2 := by positivity
      have hx1 : 2 * γ * (d : ℝ) ^ 2 < (d : ℝ) ^ 2 / 4 := by nlinarith
      have hL : ∀ q : ℝ, 0 < q → q ≤ 1 →
          2 * d * rho d γ ≤ Real.log (Pf d q) - 2 * γ * (d : ℝ) ^ 2 * Real.log q := by
        intro q hq0 hq1
        have h := mul_le_mul_of_nonneg_left (rho_le_rhoFun d hd1 hγ hq0 hq1)
          (by positivity : (0 : ℝ) ≤ 2 * d)
        rw [rhoFun_eq] at h
        have e : 2 * (d : ℝ) * (1 / (2 * d) * Real.log (Pf d q) - γ * d * Real.log q) =
            Real.log (Pf d q) - 2 * γ * (d : ℝ) ^ 2 * Real.log q := by
          field_simp
        linarith
      filter_upwards [lower_tail h8 hd1 hx0 hx1 hL (ε := d * ε) (by positivity),
        eventually_ge_atTop 1] with m hm hm1
      have hsub : (#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
          (edgesIn (KddUnion m d) A : ℝ) < m * (2 * γ * (d : ℝ) ^ 2)) : ℝ) ≤
          iGamma (KddUnion m d) d γ := by
        rw [iGamma_eq_card]
        apply Nat.cast_le.2
        apply Finset.card_le_card
        intro A hA
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
        rw [hcard]
        have : (m : ℝ) * (2 * γ * (d : ℝ) ^ 2) = γ * d * (2 * d * m) := by ring
        linarith
      have h2 := div_le_of_exp_le hd1 hm1 (hm.trans hsub)
      have e : (2 * d * rho d γ - d * ε) / (2 * d) = rho d γ - ε / 2 := by
        field_simp
      linarith
    · -- γ ≥ 1/8
      set a := d * Real.log 4 - Real.log (Pf d 0) with ha
      have ha0 : 0 ≤ a := by
        have h := Real.log_le_log (Pf_pos d le_rfl) (Pf_le_four_pow d le_rfl zero_le_one)
        rw [Real.log_pow] at h
        linarith
      set t := min (1 / 2) (d * ε / (2 * (a + 1))) with ht
      have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
      have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
      have hat : a * t ≤ d * ε / 2 := by
        have h1 : t ≤ d * ε / (2 * (a + 1)) := min_le_right _ _
        calc a * t ≤ (a + 1) * t := by nlinarith
          _ ≤ (a + 1) * (d * ε / (2 * (a + 1))) := mul_le_mul_of_nonneg_left h1 (by linarith)
          _ = d * ε / 2 := by field_simp
      set x' := (d : ℝ) ^ 2 / 4 * (1 - t) with hx'
      have hx'0 : 0 < x' := by
        have : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
        have : 0 < 1 - t := by linarith
        positivity
      have hx'1 : x' < (d : ℝ) ^ 2 / 4 := by
        have : 0 < (d : ℝ) ^ 2 / 4 := by positivity
        nlinarith
      have hL : ∀ q : ℝ, 0 < q → q ≤ 1 →
          d * Real.log 4 - a * t ≤ Real.log (Pf d q) - x' * Real.log q :=
        fun q hq0 _ => jensen_lower d hd1 ht0.le ht1 hq0
      filter_upwards [lower_tail h8 hd1 hx'0 hx'1 hL (ε := d * ε / 2) (by positivity),
        eventually_ge_atTop 1] with m hm hm1
      have hsub : (#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
          (edgesIn (KddUnion m d) A : ℝ) < m * x') : ℝ) ≤ iGamma (KddUnion m d) d γ := by
        rw [iGamma_eq_card]
        apply Nat.cast_le.2
        apply Finset.card_le_card
        intro A hA
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
        rw [hcard]
        have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have h1 : x' ≤ 2 * γ * (d : ℝ) ^ 2 := by nlinarith
        have h2 : (m : ℝ) * x' ≤ m * (2 * γ * (d : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h1 hmR
        have : (m : ℝ) * (2 * γ * (d : ℝ) ^ 2) = γ * d * (2 * d * m) := by ring
        linarith
      have h2 := div_le_of_exp_le hd1 hm1 (hm.trans hsub)
      have e : (d * Real.log 4 - a * t - d * ε / 2) / (2 * d) =
          Real.log 2 - a * t / (2 * d) - ε / 4 := by
        rw [log_four]
        field_simp
        ring
      have hat' : a * t / (2 * d) ≤ ε / 4 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith [rho_le_log_two d hd1 hγ]
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hlow ((rho d γ - a) / 2) (by linarith)] with m hm
    linarith
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact lt_of_le_of_lt (hup m hm) hb

theorem propositionC (hS : SSSZBound) (h8 : Lemma8) : PropositionC :=
  fun d hd _ hγ => ⟨fun V _ _ G _ hn hG => propC_upper hS d hd hγ V G hn hG,
    propC_limit h8 d hd hγ⟩

end P3CD
