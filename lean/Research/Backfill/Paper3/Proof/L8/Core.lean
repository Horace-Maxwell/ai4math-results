import Research.Backfill.Paper3.Proof.L8.Tilt

/-!
# Lemma 8, part 3: the lower bounds (a), (b) for sums of coefficients

For weights `a ≥ 0` on `{0, …, M}` with total mass `1`, `a 0 > 0` and `a M > 0`, the tilted mean
`tmean a M` is continuous, equals the mean at `λ = 0`, is close to `M` for large `λ` and close
to `0` for very negative `λ`. The intermediate value theorem gives a tilt whose mean is `x ± δ`
with `|λ|` bounded independently of `δ`; the window bound of `Research.Backfill.Paper3.Proof.L8.Tilt` then gives
`Σ_{s > mx} [z^s] f^m ≥ exp(m (inf_{λ ≥ 0} (log Z(λ) - λ x) - ε))` for large `m`, and the
symmetric bound for `s < mx`. Also: the two families are bounded below.
-/

set_option autoImplicit false

namespace P3L8

open Polynomial Finset Filter

theorem Zf_zero (a : ℕ → ℝ) (M : ℕ) : Zf a M 0 = ∑ i ∈ range (M + 1), a i := by
  unfold Zf
  simp

theorem tmean_zero (a : ℕ → ℝ) (M : ℕ) (hsum : ∑ i ∈ range (M + 1), a i = 1) :
    tmean a M 0 = ∑ i ∈ range (M + 1), (i : ℝ) * a i := by
  unfold tmean
  rw [Zf_zero, hsum, div_one]
  simp

theorem continuous_tmean (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (h0 : 0 < a 0) :
    Continuous (tmean a M) := by
  have hZ : Continuous (Zf a M) := by
    unfold Zf
    fun_prop
  have hN : Continuous (fun l : ℝ => ∑ i ∈ range (M + 1), (i : ℝ) * a i * Real.exp (l * i)) := by
    fun_prop
  exact hN.div hZ (fun l => (Zf_pos a M ha h0 l).ne')

theorem Zf_ge_term (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (l : ℝ) (j : ℕ) (hj : j ≤ M) :
    a j * Real.exp (l * j) ≤ Zf a M l := by
  unfold Zf
  exact single_le_sum (f := fun i : ℕ => a i * Real.exp (l * i))
    (fun i _ => mul_nonneg (ha i) (Real.exp_pos _).le) (mem_range.mpr (Nat.lt_succ_of_le hj))

/-- For `λ ≥ 0`: `tmean a M λ ≥ M - M e^{-λ} / a M`. -/
theorem tmean_ge (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (h0 : 0 < a 0)
    (hsum : ∑ i ∈ range (M + 1), a i = 1) (hM : 0 < a M) (l : ℝ) (hl : 0 ≤ l) :
    (M : ℝ) - M * Real.exp (-l) / a M ≤ tmean a M l := by
  have hZ := Zf_pos a M ha h0 l
  have hZM := Zf_ge_term a M ha l M le_rfl
  have hnum : (M : ℝ) * Zf a M l - ∑ i ∈ range (M + 1), (i : ℝ) * a i * Real.exp (l * i) ≤
      M * Real.exp (-l) * Real.exp (l * M) := by
    unfold Zf
    rw [mul_sum, ← sum_sub_distrib]
    calc ∑ i ∈ range (M + 1), ((M : ℝ) * (a i * Real.exp (l * i)) -
          (i : ℝ) * a i * Real.exp (l * i))
        ≤ ∑ i ∈ range (M + 1), a i * (M * Real.exp (-l) * Real.exp (l * M)) := by
          apply sum_le_sum
          intro i hi
          have hiM : i ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hi)
          have hai := ha i
          rcases Nat.lt_or_ge i M with hlt | hge
          · have hi1 : (i : ℝ) + 1 ≤ M := by exact_mod_cast hlt
            have hexp : Real.exp (l * i) ≤ Real.exp (-l) * Real.exp (l * M) := by
              rw [← Real.exp_add]
              apply Real.exp_le_exp.mpr
              nlinarith
            have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
            have he := (Real.exp_pos (l * i)).le
            calc (M : ℝ) * (a i * Real.exp (l * i)) - (i : ℝ) * a i * Real.exp (l * i)
                = ((M : ℝ) - i) * (a i * Real.exp (l * i)) := by ring
              _ ≤ (M : ℝ) * (a i * Real.exp (l * i)) := by nlinarith [mul_nonneg hai he]
              _ ≤ (M : ℝ) * (a i * (Real.exp (-l) * Real.exp (l * M))) := by
                  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
                  exact mul_le_mul_of_nonneg_left hexp hai
              _ = a i * (M * Real.exp (-l) * Real.exp (l * M)) := by ring
          · have hiM' : i = M := le_antisymm hiM hge
            rw [hiM']
            have hnn : 0 ≤ a M * ((M : ℝ) * Real.exp (-l) * Real.exp (l * M)) := by
              have := ha M
              positivity
            have h0' : (M : ℝ) * (a M * Real.exp (l * M)) - (M : ℝ) * a M * Real.exp (l * M) = 0 := by
              ring
            linarith
      _ = M * Real.exp (-l) * Real.exp (l * M) := by rw [← sum_mul, hsum, one_mul]
  have h1 : (M : ℝ) * Real.exp (-l) * Real.exp (l * M) / Zf a M l ≤ M * Real.exp (-l) / a M := by
    rw [div_le_div_iff₀ hZ hM]
    have hnn : 0 ≤ (M : ℝ) * Real.exp (-l) := by positivity
    calc (M : ℝ) * Real.exp (-l) * Real.exp (l * M) * a M
        = ((M : ℝ) * Real.exp (-l)) * (a M * Real.exp (l * M)) := by ring
      _ ≤ ((M : ℝ) * Real.exp (-l)) * Zf a M l := mul_le_mul_of_nonneg_left hZM hnn
  have h2 : (M : ℝ) - (M : ℝ) * Real.exp (-l) * Real.exp (l * M) / Zf a M l ≤
      (∑ i ∈ range (M + 1), (i : ℝ) * a i * Real.exp (l * i)) / Zf a M l := by
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hZ]
    linarith
  unfold tmean
  linarith

/-- For `λ ≤ 0`: `tmean a M λ ≤ M e^{λ} / a 0`. -/
theorem tmean_le (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (h0 : 0 < a 0)
    (hsum : ∑ i ∈ range (M + 1), a i = 1) (l : ℝ) (hl : l ≤ 0) :
    tmean a M l ≤ M * Real.exp l / a 0 := by
  have hZ := Zf_pos a M ha h0 l
  have hZ0 : a 0 ≤ Zf a M l := by
    have := Zf_ge_term a M ha l 0 (Nat.zero_le M)
    simpa using this
  have hnum : ∑ i ∈ range (M + 1), (i : ℝ) * a i * Real.exp (l * i) ≤ M * Real.exp l := by
    calc ∑ i ∈ range (M + 1), (i : ℝ) * a i * Real.exp (l * i)
        ≤ ∑ i ∈ range (M + 1), a i * (M * Real.exp l) := by
          apply sum_le_sum
          intro i hi
          have hiM : (i : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hi)
          have hai := ha i
          rcases Nat.eq_zero_or_pos i with h | h
          · rw [h, Nat.cast_zero, zero_mul, zero_mul]
            exact mul_nonneg (ha 0) (mul_nonneg (Nat.cast_nonneg M) (Real.exp_pos l).le)
          · have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h
            have hexp : Real.exp (l * i) ≤ Real.exp l := Real.exp_le_exp.mpr (by nlinarith)
            calc (i : ℝ) * a i * Real.exp (l * i) ≤ (M : ℝ) * a i * Real.exp (l * i) := by
                  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
                  exact mul_le_mul_of_nonneg_right hiM hai
              _ ≤ (M : ℝ) * a i * Real.exp l :=
                  mul_le_mul_of_nonneg_left hexp (mul_nonneg (Nat.cast_nonneg M) hai)
              _ = a i * (M * Real.exp l) := by ring
      _ = M * Real.exp l := by rw [← sum_mul, hsum, one_mul]
  unfold tmean
  calc (∑ i ∈ range (M + 1), (i : ℝ) * a i * Real.exp (l * i)) / Zf a M l
      ≤ M * Real.exp l / Zf a M l := div_le_div_of_nonneg_right hnum hZ.le
    _ ≤ M * Real.exp l / a 0 :=
        div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg M) (Real.exp_pos l).le) h0 hZ0

/-- The family over `λ ≥ 0` is bounded below by `log (a M)` when `x ≤ M`. -/
theorem bddBelow_Ici (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (hM : 0 < a M) (x : ℝ)
    (hx : x ≤ M) :
    BddBelow (Set.range fun l : Set.Ici (0 : ℝ) => Real.log (Zf a M l) - l * x) := by
  refine ⟨Real.log (a M), ?_⟩
  rintro _ ⟨⟨l, hl⟩, rfl⟩
  show Real.log (a M) ≤ Real.log (Zf a M l) - l * x
  have hl0 : (0 : ℝ) ≤ l := hl
  have hterm := Zf_ge_term a M ha l M le_rfl
  have hpos : 0 < a M * Real.exp (l * M) := mul_pos hM (Real.exp_pos _)
  have hlog : Real.log (a M * Real.exp (l * M)) ≤ Real.log (Zf a M l) :=
    Real.log_le_log hpos hterm
  rw [Real.log_mul hM.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  nlinarith [mul_le_mul_of_nonneg_left hx hl0]

/-- The family over `λ ≤ 0` is bounded below by `log (a 0)` when `0 ≤ x`. -/
theorem bddBelow_Iic (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (h0 : 0 < a 0) (x : ℝ)
    (hx : 0 ≤ x) :
    BddBelow (Set.range fun l : Set.Iic (0 : ℝ) => Real.log (Zf a M l) - l * x) := by
  refine ⟨Real.log (a 0), ?_⟩
  rintro _ ⟨⟨l, hl⟩, rfl⟩
  show Real.log (a 0) ≤ Real.log (Zf a M l) - l * x
  have hl0 : l ≤ 0 := hl
  have hterm := Zf_ge_term a M ha l 0 (Nat.zero_le M)
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] at hterm
  have hlog : Real.log (a 0) ≤ Real.log (Zf a M l) := Real.log_le_log h0 hterm
  nlinarith [mul_nonneg (neg_nonneg.mpr hl0) hx]

/-- The final estimate: `exp(m(I - ε)) ≤ exp(m B) (1 - M²/(mδ²))` for `B ≥ I - ε/2` and `m`
large. -/
theorem exp_bound_aux (I B ε δ : ℝ) (M m : ℕ) (hε : 0 < ε) (hδ : 0 < δ) (hB : I - ε / 2 ≤ B)
    (hm1 : 2 * (M : ℝ) ^ 2 / δ ^ 2 ≤ m) (hm2 : 2 / ε ≤ m) (hm0 : 0 < m) :
    Real.exp (m * (I - ε)) ≤ Real.exp (m * B) * (1 - (M : ℝ) ^ 2 / (m * δ ^ 2)) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hhalf : 1 / 2 ≤ 1 - (M : ℝ) ^ 2 / (m * δ ^ 2) := by
    have h : (M : ℝ) ^ 2 / (m * δ ^ 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hm1
      nlinarith
    linarith
  have hexp_half : Real.exp (-(m * (ε / 2))) ≤ 1 / 2 := by
    have h2 : 2 ≤ Real.exp (m * (ε / 2)) := by
      have h3 := Real.add_one_le_exp (m * (ε / 2))
      have h4 : 1 ≤ (m : ℝ) * (ε / 2) := by
        rw [div_le_iff₀ hε] at hm2
        nlinarith
      linarith
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  calc Real.exp (m * (I - ε))
      = Real.exp (m * (I - ε / 2)) * Real.exp (-(m * (ε / 2))) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (m * B) * (1 / 2) :=
        mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hB hmR.le)) hexp_half
          (Real.exp_pos _).le (Real.exp_pos _).le
    _ ≤ Real.exp (m * B) * (1 - (M : ℝ) ^ 2 / (m * δ ^ 2)) :=
        mul_le_mul_of_nonneg_left hhalf (Real.exp_pos _).le

/-- `m` large in the sense of `exp_bound_aux`. -/
theorem eventually_large (M : ℕ) (δ ε : ℝ) :
    ∀ᶠ m : ℕ in atTop, 2 * (M : ℝ) ^ 2 / δ ^ 2 ≤ m ∧ 2 / ε ≤ m ∧ 0 < m := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (M : ℝ) ^ 2 / δ ^ 2 + |2 / ε|)
  filter_upwards [eventually_ge_atTop (N + 1)] with m hm
  have hmN : (N : ℝ) + 1 ≤ m := by exact_mod_cast hm
  have h1 : 0 ≤ 2 * (M : ℝ) ^ 2 / δ ^ 2 := by positivity
  have h2 := le_abs_self (2 / ε)
  have h3 := abs_nonneg (2 / ε)
  refine ⟨by linarith, by linarith, by omega⟩

/-- **Part (a) for coefficient sums.** -/
theorem core_a (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i ∈ range (M + 1), a i = 1)
    (h0 : 0 < a 0) (hM : 0 < a M) (x : ℝ) (hx1 : ∑ i ∈ range (M + 1), (i : ℝ) * a i < x)
    (hx2 : x < M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.exp (m * ((⨅ l : Set.Ici (0 : ℝ), (Real.log (Zf a M l) - l * x)) - ε)) ≤
        ∑ s ∈ (range (m * M + 1)).filter (fun s : ℕ => (m : ℝ) * x < s),
          (gpoly a M ^ m).coeff s := by
  have hE0 : 0 ≤ ∑ i ∈ range (M + 1), (i : ℝ) * a i :=
    sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg i) (ha i))
  have hx0 : 0 < x := lt_of_le_of_lt hE0 hx1
  have hMx : 0 < (M : ℝ) - x := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  -- a tilt `L > 0` with `tmean L ≥ (M + x) / 2`
  set c : ℝ := a M * ((M : ℝ) - x) / (2 * M) with hc
  have hcpos : 0 < c := by positivity
  set L : ℝ := 1 / c with hL
  have hLpos : 0 < L := by positivity
  have hexpL : Real.exp (-L) ≤ c := by
    rw [Real.exp_neg]
    have h : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    calc (Real.exp L)⁻¹ ≤ L⁻¹ := inv_anti₀ hLpos h
      _ = c := by rw [hL, one_div, inv_inv]
  have htL : ((M : ℝ) + x) / 2 ≤ tmean a M L := by
    have h1 := tmean_ge a M ha h0 hsum hM L hLpos.le
    have h2 : (M : ℝ) * Real.exp (-L) / a M ≤ (M : ℝ) * c / a M :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexpL (Nat.cast_nonneg M)) hM.le
    have h3 : (M : ℝ) * c / a M = ((M : ℝ) - x) / 2 := by
      rw [hc]
      field_simp
    linarith
  -- the window half-width `δ`
  set δ : ℝ := min (((M : ℝ) - x) / 2) (ε / (4 * (L + 1))) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδ1 : δ ≤ ((M : ℝ) - x) / 2 := min_le_left _ _
  have hδ2 : δ ≤ ε / (4 * (L + 1)) := min_le_right _ _
  -- intermediate value theorem: a tilt `l ∈ [0, L]` with mean `x + δ`
  have hmem : x + δ ∈ Set.Icc (tmean a M 0) (tmean a M L) := by
    rw [tmean_zero a M hsum]
    constructor <;> linarith
  obtain ⟨l, ⟨hl0, hlL⟩, hlμ⟩ :=
    intermediate_value_Icc hLpos.le (continuous_tmean a M ha h0).continuousOn hmem
  -- the infimum is at most the value at `l`
  have hI : (⨅ l : Set.Ici (0 : ℝ), (Real.log (Zf a M l) - l * x)) ≤
      Real.log (Zf a M l) - l * x :=
    ciInf_le (bddBelow_Ici a M ha hM x hx2.le) ⟨l, hl0⟩
  have hB : (⨅ l : Set.Ici (0 : ℝ), (Real.log (Zf a M l) - l * x)) - ε / 2 ≤
      Real.log (Zf a M l) - l * tmean a M l - δ * |l| := by
    rw [hlμ, abs_of_nonneg hl0]
    have h1 : ε / (4 * (L + 1)) * L ≤ ε / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h2 : δ * l ≤ ε / (4 * (L + 1)) * L :=
      mul_le_mul hδ2 hlL hl0 (by positivity)
    nlinarith
  filter_upwards [eventually_large M δ ε] with m hm
  obtain ⟨hm1, hm2, hm0⟩ := hm
  have hwin := window_bound a M ha h0 l m hm0 δ hδpos
  have hsub : (range (m * M + 1)).filter (fun s : ℕ => |(s : ℝ) - m * tmean a M l| < m * δ) ⊆
      (range (m * M + 1)).filter (fun s : ℕ => (m : ℝ) * x < s) := by
    intro s hs
    rw [mem_filter] at hs ⊢
    refine ⟨hs.1, ?_⟩
    have h := (abs_lt.mp hs.2).1
    rw [hlμ] at h
    nlinarith
  have hmono := sum_le_sum_of_subset_of_nonneg hsub
    (fun s _ _ => coeff_gpoly_pow_nonneg a ha M m s)
  exact (exp_bound_aux _ _ ε δ M m hε hδpos hB hm1 hm2 hm0).trans (hwin.trans hmono)

/-- **Part (b) for coefficient sums.** -/
theorem core_b (a : ℕ → ℝ) (M : ℕ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i ∈ range (M + 1), a i = 1)
    (h0 : 0 < a 0) (x : ℝ) (hx1 : 0 < x) (hx2 : x < ∑ i ∈ range (M + 1), (i : ℝ) * a i)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.exp (m * ((⨅ l : Set.Iic (0 : ℝ), (Real.log (Zf a M l) - l * x)) - ε)) ≤
        ∑ s ∈ (range (m * M + 1)).filter (fun s : ℕ => (s : ℝ) < m * x),
          (gpoly a M ^ m).coeff s := by
  have hEM : ∑ i ∈ range (M + 1), (i : ℝ) * a i ≤ M := by
    calc ∑ i ∈ range (M + 1), (i : ℝ) * a i ≤ ∑ i ∈ range (M + 1), (M : ℝ) * a i := by
          apply sum_le_sum
          intro i hi
          have hiM : (i : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hi)
          exact mul_le_mul_of_nonneg_right hiM (ha i)
      _ = M := by rw [← mul_sum, hsum, mul_one]
  have hMpos : (0 : ℝ) < M := by linarith
  -- a tilt `-L < 0` with `tmean (-L) ≤ x / 2`
  set c : ℝ := a 0 * x / (2 * M) with hc
  have hcpos : 0 < c := by positivity
  set L : ℝ := 1 / c with hL
  have hLpos : 0 < L := by positivity
  have hexpL : Real.exp (-L) ≤ c := by
    rw [Real.exp_neg]
    have h : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    calc (Real.exp L)⁻¹ ≤ L⁻¹ := inv_anti₀ hLpos h
      _ = c := by rw [hL, one_div, inv_inv]
  have htL : tmean a M (-L) ≤ x / 2 := by
    have h1 := tmean_le a M ha h0 hsum (-L) (by linarith)
    have h2 : (M : ℝ) * Real.exp (-L) / a 0 ≤ (M : ℝ) * c / a 0 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexpL (Nat.cast_nonneg M)) h0.le
    have h3 : (M : ℝ) * c / a 0 = x / 2 := by
      rw [hc]
      field_simp
    linarith
  -- the window half-width `δ`
  set δ : ℝ := min (x / 2) (ε / (4 * (L + 1))) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδ1 : δ ≤ x / 2 := min_le_left _ _
  have hδ2 : δ ≤ ε / (4 * (L + 1)) := min_le_right _ _
  -- intermediate value theorem: a tilt `l ∈ [-L, 0]` with mean `x - δ`
  have hmem : x - δ ∈ Set.Icc (tmean a M (-L)) (tmean a M 0) := by
    rw [tmean_zero a M hsum]
    constructor <;> linarith
  obtain ⟨l, ⟨hlL, hl0⟩, hlμ⟩ :=
    intermediate_value_Icc (by linarith : -L ≤ 0) (continuous_tmean a M ha h0).continuousOn hmem
  have hI : (⨅ l : Set.Iic (0 : ℝ), (Real.log (Zf a M l) - l * x)) ≤
      Real.log (Zf a M l) - l * x :=
    ciInf_le (bddBelow_Iic a M ha h0 x hx1.le) ⟨l, hl0⟩
  have hB : (⨅ l : Set.Iic (0 : ℝ), (Real.log (Zf a M l) - l * x)) - ε / 2 ≤
      Real.log (Zf a M l) - l * tmean a M l - δ * |l| := by
    rw [hlμ, abs_of_nonpos hl0]
    have h1 : ε / (4 * (L + 1)) * L ≤ ε / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h2 : δ * (-l) ≤ ε / (4 * (L + 1)) * L :=
      mul_le_mul hδ2 (by linarith) (by linarith) (by positivity)
    nlinarith
  filter_upwards [eventually_large M δ ε] with m hm
  obtain ⟨hm1, hm2, hm0⟩ := hm
  have hwin := window_bound a M ha h0 l m hm0 δ hδpos
  have hsub : (range (m * M + 1)).filter (fun s : ℕ => |(s : ℝ) - m * tmean a M l| < m * δ) ⊆
      (range (m * M + 1)).filter (fun s : ℕ => (s : ℝ) < m * x) := by
    intro s hs
    rw [mem_filter] at hs ⊢
    refine ⟨hs.1, ?_⟩
    have h := (abs_lt.mp hs.2).2
    rw [hlμ] at h
    nlinarith
  have hmono := sum_le_sum_of_subset_of_nonneg hsub
    (fun s _ _ => coeff_gpoly_pow_nonneg a ha M m s)
  exact (exp_bound_aux _ _ ε δ M m hε hδpos hB hm1 hm2 hm0).trans (hwin.trans hmono)

end P3L8
