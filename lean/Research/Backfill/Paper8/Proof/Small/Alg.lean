import Research.Backfill.Paper8.Proof.Small.Irr

/-!
# Paper 8, Proposition 5.1: the algebra of condition (S)

For each family of Proposition 5.1, with `t = θ²` a root of the secular polynomial `R` (written
out explicitly), the value `G(θ)` of the switching is nonzero. (a): `E² = k` only for `k ∈ {1, 4}`.
(b): `G·t(t-1) + (1+θ)R = θ(θ²-2)(θ²+θ-1)`. (c) and (d) with `k₁ ≥ 2`: squaring and reducing
modulo `R` gives an integer linear relation in `t` with nonzero constant term, impossible as `t`
is irrational (`lin_rel_trivial`). (d) with `k₁ = 1`: `θ³ = -1`. (e): `k₁θ = -2`.
-/

set_option autoImplicit false

namespace P8Small

theorem sq_ne_zero_of_R {θ : ℝ} {k0 k1 : ℝ} (hk0 : k0 ≠ 0)
    (hR : θ ^ 2 * (θ ^ 2 - 1) - (k0 * (θ ^ 2 - 1) + k1 * θ ^ 2) = 0) : θ ^ 2 ≠ 0 := by
  intro h
  rw [h] at hR
  apply hk0
  linarith

theorem sq_sub_one_ne_zero_of_R {θ : ℝ} {k0 k1 : ℝ} (hk1 : k1 ≠ 0)
    (hR : θ ^ 2 * (θ ^ 2 - 1) - (k0 * (θ ^ 2 - 1) + k1 * θ ^ 2) = 0) : θ ^ 2 - 1 ≠ 0 := by
  intro h
  have h1 : θ ^ 2 = 1 := by linarith
  rw [h1] at hR
  apply hk1
  linarith

/-- (a) The star `K_{1,k}` with `E = k - 2|U|`, `|U| = 2` if `k = 4` and `1` otherwise. -/
theorem caseA_alg (k u : ℕ) (hk : 2 ≤ k) (hu : u = if k = 4 then 2 else 1) (θ : ℝ)
    (ht : θ ^ 2 = k) : ((k : ℝ) + ((k : ℝ) - 2 * u) * θ) / θ ^ 2 ≠ 0 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [ht]
  intro hG
  rw [div_eq_zero_iff] at hG
  rcases hG with hG | hG
  · have hE : ((k : ℝ) - 2 * u) ^ 2 * k = (k : ℝ) ^ 2 := by
      have h1 : ((k : ℝ) - 2 * u) * θ = -k := by linarith
      calc ((k : ℝ) - 2 * u) ^ 2 * k = (((k : ℝ) - 2 * u) * θ) ^ 2 := by rw [mul_pow, ht]
        _ = (k : ℝ) ^ 2 := by rw [h1]; ring
    have hE' : ((k : ℝ) - 2 * u) ^ 2 = k := by
      have hkne : (k : ℝ) ≠ 0 := by positivity
      apply mul_right_cancel₀ hkne
      rw [hE]
      ring
    by_cases h4 : k = 4
    · simp only [h4, ite_true] at hu
      subst hu
      rw [h4] at hE'
      norm_num at hE'
    · simp only [h4, ite_false] at hu
      subst hu
      have h14 : ((k : ℝ) - 1) * ((k : ℝ) - 4) = 0 := by linear_combination hE'
      rcases mul_eq_zero.1 h14 with h | h
      · have : (k : ℝ) = 1 := by linarith
        have : k = 1 := by exact_mod_cast this
        omega
      · have : (k : ℝ) = 4 := by linarith
        have : k = 4 := by exact_mod_cast this
        exact h4 this
  · linarith

/-- (b) `k₁ = 1`, `k₀ ≥ 2`: `G = (k₀ + (k₀-2)θ)/t + θ/(t-1)`. -/
theorem caseB_alg (k0 : ℕ) (hk0 : 2 ≤ k0) (θ : ℝ)
    (hR : θ ^ 2 * (θ ^ 2 - 1) - ((k0 : ℝ) * (θ ^ 2 - 1) + 1 * θ ^ 2) = 0) :
    ((k0 : ℝ) + ((k0 : ℝ) - 2) * θ) / θ ^ 2 + θ / (θ ^ 2 - 1) ≠ 0 := by
  have hk0' : (2 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have ht0 := sq_ne_zero_of_R (by positivity) hR
  have ht1 := sq_sub_one_ne_zero_of_R one_ne_zero hR
  intro hG
  rw [div_add_div _ _ ht0 ht1, div_eq_zero_iff] at hG
  rcases hG with hG | hG
  · have key : θ * ((θ ^ 2 - 2) * (θ ^ 2 + θ - 1)) = 0 := by
      linear_combination hG + (1 + θ) * hR
    rcases mul_eq_zero.1 key with h | h
    · apply ht0
      rw [h]
      ring
    rcases mul_eq_zero.1 h with h | h
    · have h2 : θ ^ 2 = 2 := by linarith
      rw [h2] at hR
      linarith
    · have h4 : θ ^ 4 - 3 * θ ^ 2 + 1 = 0 := by linear_combination (θ ^ 2 - θ - 1) * h
      have h5 : ((k0 : ℝ) - 1) * (θ ^ 2 - 1) = 0 := by linear_combination -hR + h4
      rcases mul_eq_zero.1 h5 with h6 | h6
      · linarith
      · exact ht1 h6
  · exact mul_ne_zero ht0 ht1 hG

/-- The constant term `c₀` of Proposition 5.1(c) is positive. -/
theorem c0_pos (K0 K1 : ℤ) (hK0 : 2 ≤ K0) (hK1 : 2 ≤ K1) :
    0 < K0 ^ 3 + 2 * K0 ^ 2 * K1 - 6 * K0 ^ 2 + K0 * K1 ^ 2 - 7 * K0 * K1 + 13 * K0 - 4 := by
  have hX : 3 ≤ (K0 + K1 - 3) ^ 2 - K1 + 4 := by nlinarith
  have he : K0 ^ 3 + 2 * K0 ^ 2 * K1 - 6 * K0 ^ 2 + K0 * K1 ^ 2 - 7 * K0 * K1 + 13 * K0 - 4 =
      K0 * ((K0 + K1 - 3) ^ 2 - K1 + 4) - 4 := by ring
  rw [he]
  nlinarith

/-- (c) `k₀, k₁ ≥ 2`: `G = (k₀ + (k₀-2)θ)/t + (2k₁ - 2 + k₁θ)/(t-1)`. -/
theorem caseC_alg (k0 k1 : ℕ) (hk0 : 2 ≤ k0) (hk1 : 2 ≤ k1) (θ : ℝ)
    (hR : θ ^ 2 * (θ ^ 2 - 1) - ((k0 : ℝ) * (θ ^ 2 - 1) + (k1 : ℝ) * θ ^ 2) = 0) :
    ((k0 : ℝ) + ((k0 : ℝ) - 2) * θ) / θ ^ 2 +
      (2 * (k1 : ℝ) - 2 + (k1 : ℝ) * θ) / (θ ^ 2 - 1) ≠ 0 := by
  have hk0' : (2 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hk1' : (2 : ℝ) ≤ k1 := by exact_mod_cast hk1
  have ht0 := sq_ne_zero_of_R (by positivity) hR
  have ht1 := sq_sub_one_ne_zero_of_R (by positivity) hR
  intro hG
  rw [div_add_div _ _ ht0 ht1, div_eq_zero_iff] at hG
  rcases hG with hG | hG
  · -- `G·t(t-1) = t(t+k₁-3) + θ(t-1)(t-2)` modulo `R`
    have hE : θ ^ 2 * (θ ^ 2 + k1 - 3) + θ * (θ ^ 2 - 1) * (θ ^ 2 - 2) = 0 := by
      linear_combination hG + (1 + θ) * hR
    -- squaring and reducing modulo `R`: `c₁ t + c₀ = 0`
    obtain ⟨K0, hK0⟩ : ∃ K0 : ℤ, K0 = k0 := ⟨_, rfl⟩
    obtain ⟨K1, hK1⟩ : ∃ K1 : ℤ, K1 = k1 := ⟨_, rfl⟩
    have e0 : (k0 : ℝ) = (K0 : ℝ) := by rw [hK0]; push_cast; rfl
    have e1 : (k1 : ℝ) = (K1 : ℝ) := by rw [hK1]; push_cast; rfl
    rw [e0, e1] at hR
    rw [e1] at hE
    obtain ⟨C1, hC1⟩ : ∃ C1 : ℤ, C1 = -K0 ^ 3 - 3 * K0 ^ 2 * K1 + 6 * K0 ^ 2 - 3 * K0 * K1 ^ 2 +
      12 * K0 * K1 - 13 * K0 - K1 ^ 3 + 7 * K1 ^ 2 - 12 * K1 + 8 := ⟨_, rfl⟩
    obtain ⟨C0, hC0⟩ : ∃ C0 : ℤ, C0 = K0 ^ 3 + 2 * K0 ^ 2 * K1 - 6 * K0 ^ 2 + K0 * K1 ^ 2 -
      7 * K0 * K1 + 13 * K0 - 4 := ⟨_, rfl⟩
    have hlin0 : θ ^ 2 * ((C1 : ℝ) * θ ^ 2 + C0) = 0 := by
      rw [hC1, hC0]
      push_cast
      linear_combination (θ ^ 2 * (θ ^ 2 + K1 - 3) - θ * (θ ^ 2 - 1) * (θ ^ 2 - 2)) * hE -
        θ ^ 2 * (-(θ ^ 2) ^ 2 + θ ^ 2 * (6 - K0 - K1) - K0 ^ 2 - 2 * K0 * K1 + 6 * K0 - K1 ^ 2 +
          7 * K1 - 13) * hR
    have hlin : (C1 : ℝ) * θ ^ 2 + C0 = 0 := by
      rcases mul_eq_zero.1 hlin0 with h | h
      · exact absurd h ht0
      · exact h
    have hq : (θ ^ 2) ^ 2 - ((1 + K0 + K1 : ℤ) : ℝ) * θ ^ 2 + ((K0 : ℤ) : ℝ) = 0 := by
      push_cast
      linear_combination hR
    have hK0' : 2 ≤ K0 := by omega
    have hK1' : 2 ≤ K1 := by omega
    have hns : ∀ y : ℤ, y ^ 2 ≠ (1 + K0 + K1) ^ 2 - 4 * K0 := by
      apply not_square_of_between (by omega) (by omega)
      nlinarith
    obtain ⟨-, h0⟩ := lin_rel_trivial hq hns hlin
    have := c0_pos K0 K1 hK0' hK1'
    rw [← hC0, h0] at this
    exact lt_irrefl _ this
  · exact mul_ne_zero ht0 ht1 hG

/-- (d) with `k₁ = 1` (`k₀ = 1`): `G = (1 + θ)/t + θ/(t-1)`. -/
theorem caseD1_alg (θ : ℝ)
    (hR : θ ^ 2 * (θ ^ 2 - 1) - (1 * (θ ^ 2 - 1) + 1 * θ ^ 2) = 0) :
    (1 + θ) / θ ^ 2 + θ / (θ ^ 2 - 1) ≠ 0 := by
  have ht0 := sq_ne_zero_of_R one_ne_zero hR
  have ht1 := sq_sub_one_ne_zero_of_R one_ne_zero hR
  intro hG
  rw [div_add_div _ _ ht0 ht1, div_eq_zero_iff] at hG
  rcases hG with hG | hG
  · have h1 : (θ ^ 2 - 1) * (1 + θ * θ ^ 2) = 0 := by linear_combination hG + θ * hR
    rcases mul_eq_zero.1 h1 with h | h
    · exact ht1 h
    · have h2 : (θ + 1) * (θ ^ 2 - θ + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h2 with h3 | h3
      · apply ht1
        have : θ = -1 := by linarith
        rw [this]
        ring
      · nlinarith [sq_nonneg (2 * θ - 1)]
  · exact mul_ne_zero ht0 ht1 hG

/-- (d) with `k₁ ≥ 2` (`k₀ = 1`): `G = (1 + θ)/t + (2 + k₁θ)/(t-1)`. -/
theorem caseD2_alg (k1 : ℕ) (hk1 : 2 ≤ k1) (θ : ℝ)
    (hR : θ ^ 2 * (θ ^ 2 - 1) - (1 * (θ ^ 2 - 1) + (k1 : ℝ) * θ ^ 2) = 0) :
    (1 + θ) / θ ^ 2 + (2 + (k1 : ℝ) * θ) / (θ ^ 2 - 1) ≠ 0 := by
  have hk1' : (2 : ℝ) ≤ k1 := by exact_mod_cast hk1
  have ht0 := sq_ne_zero_of_R one_ne_zero hR
  have ht1 := sq_sub_one_ne_zero_of_R (by positivity) hR
  intro hG
  rw [div_add_div _ _ ht0 ht1, div_eq_zero_iff] at hG
  rcases hG with hG | hG
  · have hE : (3 * θ ^ 2 - 1) + θ * θ ^ 2 * (θ ^ 2 - 1) = 0 := by
      linear_combination hG + θ * hR
    obtain ⟨K1, hK1⟩ : ∃ K1 : ℤ, K1 = k1 := ⟨_, rfl⟩
    have e1 : (k1 : ℝ) = (K1 : ℝ) := by rw [hK1]; push_cast; rfl
    rw [e1] at hR
    obtain ⟨D1, hD1⟩ : ∃ D1 : ℤ, D1 = (K1 - 1) * (K1 ^ 3 + 7 * K1 ^ 2 + 17 * K1 + 12) := ⟨_, rfl⟩
    obtain ⟨D0, hD0⟩ : ∃ D0 : ℤ, D0 = -((K1 - 1) * (K1 ^ 2 + 5 * K1 + 8)) := ⟨_, rfl⟩
    have hlin : (D1 : ℝ) * θ ^ 2 + D0 = 0 := by
      rw [hD1, hD0]
      push_cast
      linear_combination (θ * θ ^ 2 * (θ ^ 2 - 1) - (3 * θ ^ 2 - 1)) * hE -
        (K1 ^ 3 + 4 * K1 ^ 2 + K1 * (θ ^ 2) ^ 2 + 3 * K1 + (θ ^ 2) ^ 3 +
          θ ^ 2 * (K1 ^ 2 + 2 * K1) - 9) * hR
    have hq : (θ ^ 2) ^ 2 - ((K1 + 2 : ℤ) : ℝ) * θ ^ 2 + ((1 : ℤ) : ℝ) = 0 := by
      push_cast
      linear_combination hR
    have hK1' : 2 ≤ K1 := by omega
    have hns : ∀ y : ℤ, y ^ 2 ≠ (K1 + 2) ^ 2 - 4 * 1 := by
      apply not_square_of_between (by omega) (by omega)
      nlinarith
    obtain ⟨-, h0⟩ := lin_rel_trivial hq hns hlin
    have h1 : 0 < (K1 - 1) * (K1 ^ 2 + 5 * K1 + 8) := by
      apply mul_pos <;> nlinarith
    rw [hD0] at h0
    linarith
  · exact mul_ne_zero ht0 ht1 hG

/-- (e) `k₀ = 0`, `k₁ ≥ 2`: `R(t) = t - 1 - k₁` and `G = (2 + k₁θ)/(t-1)`. -/
theorem caseE2_alg (k1 : ℕ) (hk1 : 2 ≤ k1) (θ : ℝ) (hR : θ ^ 2 - 1 - (k1 : ℝ) = 0) :
    (2 + (k1 : ℝ) * θ) / (θ ^ 2 - 1) ≠ 0 := by
  have hk1' : (2 : ℝ) ≤ k1 := by exact_mod_cast hk1
  have ht : θ ^ 2 - 1 = k1 := by linarith
  rw [ht]
  intro hG
  rw [div_eq_zero_iff] at hG
  rcases hG with hG | hG
  · have h1 : (k1 : ℝ) * θ = -2 := by linarith
    have h2 : (k1 : ℝ) ^ 2 * (1 + k1) = 4 := by
      have : (k1 : ℝ) ^ 2 * θ ^ 2 = 4 := by
        rw [← mul_pow, h1]
        norm_num
      rw [← this]
      congr 1
      linarith
    nlinarith
  · linarith

end P8Small
