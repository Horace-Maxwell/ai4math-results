import Research.Backfill.Paper3.Proof.B.TheoremB

/-!
# Corollary 5

`N_{≤1}(G) = [z^0] P_G + [z^1] P_G`; with `P_{G ∪ F} = P_G P_F`, `P_{m K_{d,d}} = P_d^m`,
`[z^0] P_d = 2^{d+1} - 1`, `[z^1] P_d = d²` and the counts of Theorem B, the difference
`N_{≤1}(S_d ∪ (m-1) K_{d,d}) - N_{≤1}(m K_{d,d})` is a polynomial identity. The list of `(d, m)`:
direct evaluation for `d ≤ 13`, and `2^{d+1} > 2d² + 8` for `d ≥ 14`.
-/

set_option autoImplicit false

namespace P3B

open Finset SimpleGraph Polynomial BackfillPaper3.Challenge

/-! ## Coefficients 0 and 1 -/

theorem coeff_one_mul (p q : ℤ[X]) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp

theorem coeff_zero_pow' (p : ℤ[X]) (k : ℕ) : (p ^ k).coeff 0 = p.coeff 0 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Polynomial.mul_coeff_zero, ih, pow_succ]

theorem coeff_one_pow' (p : ℤ[X]) (k : ℕ) :
    (p ^ (k + 1)).coeff 1 = ((k : ℤ) + 1) * p.coeff 0 ^ k * p.coeff 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, coeff_one_mul, ih, coeff_zero_pow']
    push_cast
    ring

theorem coeff_zero_eq_iCount {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (edgePoly G).coeff 0 = (iCount G 0 : ℤ) := by
  rw [P3Basic.iCount_eq_sum_coeff]
  simp

theorem coeff_zero_add_one_eq_iCount {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (edgePoly G).coeff 0 + (edgePoly G).coeff 1 = (iCount G 1 : ℤ) := by
  rw [P3Basic.iCount_eq_sum_coeff]
  simp [Finset.sum_range_succ]

theorem pd_coeff_zero (d : ℕ) : (Pd d).coeff 0 = 2 ^ (d + 1) - 1 := by
  rw [← P3Basic.edgePoly_Kdd, coeff_zero_eq_iCount, P3Basic.check_KddIndependentSets]
  have h : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
  push_cast [h]
  ring

theorem pd_coeff_one (d : ℕ) : (Pd d).coeff 1 = (d : ℤ) ^ 2 := by
  have h := coeff_zero_add_one_eq_iCount (Kdd d)
  rw [P3Basic.edgePoly_Kdd, pd_coeff_zero, iCount_kdd_one] at h
  have h1 : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
  push_cast [h1] at h
  linarith

theorem kddUnion_poly (m d : ℕ) : edgePoly (KddUnion m d) = Pd d ^ m :=
  P3Basic.check_PolyFacts.2.2.1 m d

/-! ## The identity -/

section

variable {d : ℕ} {a₁ a₂ b₁ b₂ : Fin d}

theorem cor5_diff (hd : 3 ≤ d) {m : ℕ} (hm : 2 ≤ m) (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) :
    (iCount (Sd d a₁ a₂ b₁ b₂ ⊕g KddUnion (m - 1) d) 1 : ℤ) - iCount (KddUnion m d) 1 =
      (2 ^ (d + 1) - 1) ^ (m - 2) *
        ((4 * (d : ℤ) - 8) * (2 ^ (d + 1) - 1) -
          ((m : ℤ) - 1) * (d : ℤ) ^ 2 * (2 ^ (d - 1) - 2)) := by
  have hS0 := coeff_zero_eq_iCount (Sd d a₁ a₂ b₁ b₂)
  have hS1 := coeff_zero_add_one_eq_iCount (Sd d a₁ a₂ b₁ b₂)
  rw [iCount_sd_zero ha hb (by omega)] at hS0
  rw [iCount_sd_one_int hd ha hb] at hS1
  rw [← coeff_zero_add_one_eq_iCount, ← coeff_zero_add_one_eq_iCount, P3Basic.edgePoly_sum,
    kddUnion_poly, kddUnion_poly]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 + 1 := ⟨m - 2, by omega⟩
  rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 + 1 - 2 = k by omega,
    Polynomial.mul_coeff_zero, coeff_one_mul, coeff_zero_pow', coeff_zero_pow', coeff_one_pow',
    coeff_one_pow', pd_coeff_zero, pd_coeff_one]
  have hS1' : (edgePoly (Sd d a₁ a₂ b₁ b₂)).coeff 1 =
      2 ^ (d + 1) + (d : ℤ) ^ 2 + 4 * d - 9 - (((3 * 2 ^ (d - 1) + 1 : ℕ)) : ℤ) := by
    linarith
  rw [hS1', hS0]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [show e + 1 - 1 = e by omega]
  push_cast
  ring

/-- For `n = 2dm` and `γ ∈ [1/(dn), 2/(dn))`, `⌊γ d n⌋ = 1`. -/
theorem floor_cor5 (hd : 1 ≤ d) {m : ℕ} (hm : 1 ≤ m) {γ : ℝ}
    (h1 : 1 / ((d : ℝ) * (2 * d * m)) ≤ γ) (h2 : γ < 2 / ((d : ℝ) * (2 * d * m))) :
    ⌊γ * d * ((2 * d * m : ℕ) : ℝ)⌋₊ = 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : (0 : ℝ) < (d : ℝ) * (2 * d * m) := by positivity
  have e1 : 1 ≤ γ * ((d : ℝ) * (2 * d * m)) := (div_le_iff₀ hN).mp h1
  have e2 : γ * ((d : ℝ) * (2 * d * m)) < 2 := (lt_div_iff₀ hN).mp h2
  have hγ : 0 ≤ γ := le_trans (by positivity) h1
  rw [Nat.floor_eq_iff (by positivity)]
  push_cast
  constructor <;> nlinarith

theorem card_cor5 (d m : ℕ) (hm : 1 ≤ m) :
    Fintype.card ((Fin d ⊕ Fin d) ⊕ (Fin (m - 1) × (Fin d ⊕ Fin d))) = 2 * d * m := by
  rw [Fintype.card_sum, P3Basic.card_KddUnion, card_sum_fin]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega]
  ring

theorem cor5_gamma (hd : 3 ≤ d) {m : ℕ} (hm : 2 ≤ m) (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) {γ : ℝ}
    (h1 : 1 / ((d : ℝ) * (2 * d * m)) ≤ γ) (h2 : γ < 2 / ((d : ℝ) * (2 * d * m))) :
    iGamma (KddUnion m d) d γ < iGamma (Sd d a₁ a₂ b₁ b₂ ⊕g KddUnion (m - 1) d) d γ ↔
      ((m : ℤ) - 1) * (d : ℤ) ^ 2 * (2 ^ (d - 1) - 2) < (4 * (d : ℤ) - 8) * (2 ^ (d + 1) - 1) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hγ : 0 ≤ γ := le_trans (by positivity) h1
  rw [P3Basic.iGamma_eq_iCount_floor _ _ hγ, P3Basic.iGamma_eq_iCount_floor _ _ hγ,
    P3Basic.card_KddUnion, card_cor5 d m (by omega), floor_cor5 (by omega) (by omega) h1 h2]
  have hdiff := cor5_diff hd hm ha hb
  have hI : (0 : ℤ) < (2 ^ (d + 1) - 1) ^ (m - 2) := by
    have : (2 : ℤ) ≤ 2 ^ (d + 1) := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact pow_pos (by linarith) _
  constructor
  · intro hlt
    have hpos : (0 : ℤ) < (2 ^ (d + 1) - 1) ^ (m - 2) *
        ((4 * (d : ℤ) - 8) * (2 ^ (d + 1) - 1) -
          ((m : ℤ) - 1) * (d : ℤ) ^ 2 * (2 ^ (d - 1) - 2)) := by
      rw [← hdiff]
      omega
    have := (pos_iff_pos_of_mul_pos hpos).mp hI
    linarith
  · intro hc
    have hpos : (0 : ℤ) < (2 ^ (d + 1) - 1) ^ (m - 2) *
        ((4 * (d : ℤ) - 8) * (2 ^ (d + 1) - 1) -
          ((m : ℤ) - 1) * (d : ℤ) ^ 2 * (2 ^ (d - 1) - 2)) := mul_pos hI (by linarith)
    rw [← hdiff] at hpos
    omega

end

/-! ## The list of `(d, m)` -/

theorem two_pow_gt (d : ℕ) (hd : 14 ≤ d) : 2 * d ^ 2 + 8 < 2 ^ (d + 1) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 (n + 1)]
    nlinarith

theorem cor5_list (d m : ℕ) (hd : 3 ≤ d) (hm : 2 ≤ m) :
    ((m : ℤ) - 1) * (d : ℤ) ^ 2 * (2 ^ (d - 1) - 2) < (4 * (d : ℤ) - 8) * (2 ^ (d + 1) - 1) ↔
      (d = 3 ∧ m ≤ 4) ∨ ((d = 4 ∨ d = 5) ∧ m ≤ 3) ∨ (6 ≤ d ∧ d ≤ 13 ∧ m = 2) := by
  rcases Nat.lt_or_ge d 14 with hd14 | hd14
  · interval_cases d <;> norm_num <;> omega
  · have hR : ¬ ((d = 3 ∧ m ≤ 4) ∨ ((d = 4 ∨ d = 5) ∧ m ≤ 3) ∨ (6 ≤ d ∧ d ≤ 13 ∧ m = 2)) := by
      omega
    simp only [hR, iff_false, not_lt]
    have hpow := two_pow_gt d hd14
    obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
    rw [show j + 1 - 1 = j by omega]
    have hX : (2 * ((j : ℤ) + 1) ^ 2 + 8 : ℤ) < 2 ^ j * 4 := by
      have := (Nat.cast_lt (α := ℤ)).mpr hpow
      push_cast at this
      rw [pow_succ (2 : ℤ) (j + 1), pow_succ (2 : ℤ) j] at this
      linarith
    push_cast
    have hj : (13 : ℤ) ≤ j := by exact_mod_cast (show 13 ≤ j by omega)
    have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
    have hX0 : (0 : ℤ) ≤ 2 ^ j := by positivity
    have hX2 : (2 : ℤ) ≤ 2 ^ j := by nlinarith
    have k1 : (0 : ℤ) ≤ ((m : ℤ) - 2) * (((j : ℤ) + 1) ^ 2 * (2 ^ j - 2)) :=
      mul_nonneg (by linarith) (mul_nonneg (sq_nonneg _) (by linarith))
    have k2 : (0 : ℤ) ≤ 2 ^ j * (((j : ℤ) + 1 - 14) * ((j : ℤ) + 1 - 2)) :=
      mul_nonneg hX0 (mul_nonneg (by linarith) (by linarith))
    rw [pow_succ (2 : ℤ) (j + 1), pow_succ (2 : ℤ) j]
    nlinarith

theorem corollary5 : Corollary5 := by
  refine ⟨fun d m hd hm a₁ a₂ b₁ b₂ ha hb => ⟨cor5_diff hd hm ha hb,
    fun γ h1 h2 => cor5_gamma hd hm ha hb h1 h2⟩, cor5_list,
    fun d hd a₁ a₂ b₁ b₂ ha hb => iCount_sd_zero ha hb (by omega)⟩

end P3B
