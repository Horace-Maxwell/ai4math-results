import Research.TaskV.FEI.Challenge

namespace Fei
open Finset

private lemma support_positive {n : ℕ} {f : Cube n → Bool}
    (h : ∑ s ∈ support f, mass f s = 1) : 0 < ((support f).card : ℝ) := by
  have hne : (support f).Nonempty := by
    by_contra! hempty
    simp [hempty] at h
  exact_mod_cast Finset.card_pos.mpr hne

private lemma coeff_ne_on_support {n : ℕ} {f : Cube n → Bool} {s : Cube n}
    (hs : s ∈ support f) : coeff f s ≠ 0 := by
  classical
  simpa [support] using hs

private lemma entropy_bounds {α : Type*} (u : Finset α) (p : α → ℝ)
    (hk : 0 < (u.card : ℝ)) (hp : ∀ s ∈ u, 0 < p s) (hsum : ∑ s ∈ u, p s = 1) :
    (∑ s ∈ u, p s * (-Real.logb 2 (p s))) ≤ Real.logb 2 u.card ∧
    (u.card : ℝ) * Real.logb 2 u.card ≤ ∑ s ∈ u, -Real.logb 2 (p s) := by
  classical
  have hk0 := hk.ne'
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hweighted : ∀ s ∈ u, -(p s * Real.log (p s)) - p s * Real.log u.card ≤
      (u.card : ℝ)⁻¹ - p s := by
    intro s hs
    have hp' := hp s hs
    have h := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos (mul_pos hk hp')) hp'.le
    rw [Real.log_mul hk0 hp'.ne', mul_sub, mul_one, mul_inv_rev] at h
    have hcancel : p s * ((p s)⁻¹ * (u.card : ℝ)⁻¹) = (u.card : ℝ)⁻¹ := by
      field_simp
    rw [hcancel] at h
    linarith
  have hunweighted : ∀ s ∈ u, Real.log u.card + Real.log (p s) ≤ (u.card : ℝ) * p s - 1 := by
    intro s hs
    have hp' := hp s hs
    simpa [Real.log_mul hk0 hp'.ne'] using Real.log_le_sub_one_of_pos (mul_pos hk hp')
  have h1 := Finset.sum_le_sum hweighted
  have h2 := Finset.sum_le_sum hunweighted
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul,
    Finset.sum_const, nsmul_eq_mul, hsum, one_mul, mul_inv_cancel₀ hk0] at h1
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum, hsum, mul_one, sub_self] at h2
  constructor
  · simp_rw [Real.logb, ← neg_div, ← mul_div_assoc]
    rw [← Finset.sum_div]
    apply (div_le_div_iff_of_pos_right hlog).2
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
    linarith
  · simp_rw [Real.logb, ← neg_div, ← mul_div_assoc]
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    exact (div_le_div_iff_of_pos_right hlog).2 (by linarith)

/-- Taking logarithms preserves the divisibility gain on any subset of the spectrum. -/
theorem upper_log {n : ℕ} (f : Cube n → Bool) (V : Finset (Cube n)) (hV : V ⊆ support f)
    (h : ∃ z : ℤ, z ≠ 0 ∧
      (2 : ℝ) ^ (2 * ∑ s ∈ V, s.card) * (∏ s ∈ V, coeff f s) =
        (2 : ℝ) ^ (V.erase ∅).card * (z : ℝ)) :
    (∑ s ∈ V, -Real.logb 2 (mass f s)) + 2 * ((V.erase ∅).card : ℝ) ≤
      (4 : ℝ) * (∑ s ∈ V, s.card : ℕ) := by
  classical
  have hcoeff : ∀ s ∈ V, coeff f s ≠ 0 := fun _ h => coeff_ne_on_support (hV h)
  obtain ⟨z, hz, heq⟩ := h
  have hz' : (z : ℝ) ≠ 0 := by exact_mod_cast hz
  have hlog := congrArg (Real.logb 2) heq
  rw [Real.logb_mul (by positivity) (Finset.prod_ne_zero_iff.mpr hcoeff),
    Real.logb_mul (by positivity) hz', Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), Real.logb_prod V (coeff f) hcoeff] at hlog
  have hzlog : 0 ≤ Real.logb 2 (z : ℝ) :=
    div_nonneg (Real.log_intCast_nonneg z) (Real.log_pos (by norm_num)).le
  simp only [mass, Real.logb_pow, Nat.cast_ofNat, Finset.sum_neg_distrib, ← Finset.mul_sum]
  push_cast at hlog ⊢
  linarith

theorem supportEntropy_of (hs : SignedProduct)
    (hp : ∀ (n : ℕ) (f : Cube n → Bool), ∑ s ∈ support f, mass f s = 1) :
    SupportEntropy := by
  intro n f
  have hpos : ∀ s ∈ support f, 0 < mass f s :=
    fun _ h => sq_pos_of_ne_zero (coeff_ne_on_support h)
  obtain ⟨ha, hb⟩ := entropy_bounds (support f) (mass f) (support_positive (hp n f)) hpos (hp n f)
  exact ⟨ha, hb, upper_log f (support f) Finset.Subset.rfl (hs n f)⟩

theorem lowerMassFEI_of (hs : SupportEntropy)
    (hp : ∀ (n : ℕ) (f : Cube n → Bool), ∑ s ∈ support f, mass f s = 1) :
    LowerMassFEI := by
  intro n f δ hδ hlower
  obtain ⟨hent, hcard, hprod⟩ := hs n f
  have hk := support_positive (hp n f)
  have hbase : (support f).card * entropy f + 2 * nonemptyCount f ≤ 4 * (weightSum f : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hent hk.le
    linarith
  have hweighted : δ * (weightSum f : ℝ) ≤ (support f).card * influence f := by
    simp only [weightSum, influence, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun s hs => by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hlower s hs) (show 0 ≤ (s.card : ℝ) by positivity)
  apply (le_of_mul_le_mul_left (a := ((support f).card : ℝ)) _ hk)
  have hscale := mul_le_mul_of_nonneg_left hbase hδ.le
  calc
    (support f).card * (δ * (entropy f + 2 * nonemptyCount f / (support f).card)) =
      δ * ((support f).card * entropy f + 2 * nonemptyCount f) := by field_simp
    _ ≤ δ * (4 * (weightSum f : ℝ)) := hscale
    _ ≤ (support f).card * (4 * influence f) := by linarith

theorem boundedRatioFEI_of (hl : LowerMassFEI)
    (hp : ∀ (n : ℕ) (f : Cube n → Bool), ∑ s ∈ support f, mass f s = 1) :
    BoundedRatioFEI := by
  intro n f M hM hratio
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hMsq : 0 < M^2 := by positivity
  have hlower : ∀ t ∈ support f, (M^2)⁻¹ ≤ (support f).card * mass f t := by
    intro t ht
    have hpair : ∀ s ∈ support f, mass f s ≤ M^2 * mass f t := by
      intro s hs
      have h := pow_le_pow_left₀ (abs_nonneg (coeff f s)) (hratio s hs t ht) 2
      simpa only [mass, mul_pow, sq_abs] using h
    have hsum := Finset.sum_le_sum hpair
    rw [hp n f, Finset.sum_const, nsmul_eq_mul] at hsum
    apply (inv_le_iff_one_le_mul₀ hMsq).2
    linarith
  have h := hl n f (M^2)⁻¹ (inv_pos.mpr hMsq) hlower
  have hnonneg : 0 ≤ 2 * (nonemptyCount f : ℝ) / ((support f).card : ℝ) := by positivity
  have h' := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnonneg) (inv_pos.mpr hMsq).le).trans h
  rw [← div_eq_inv_mul] at h'
  have := (div_le_iff₀ hMsq).mp h'
  linarith

end Fei
