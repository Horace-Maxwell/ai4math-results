import Research.Backfill.Paper3.Proof.CD.Psi
import Research.Backfill.Paper3.Proof.CD.ThmD

/-!
# Remark 10(a) and reading R6

For `x > d²/4` there is `q > 1` with `ψ_x(q) < ψ_x(1)`, i.e. `c = P_d(q) q^{-x} / 4^d < 1`, and the
Markov bound gives `#{A ⊆ V(mK) : e(A) > mx} ≤ c^m 2^{2dm}` for every `m` (`upper_decay`). With
`x = 2γd²`, `γ > 1/8`, this is the exponential decay of `U(mK)/i_γ(mK)` and gives
`i_γ(mK)/2^n → 1`; reading R6 follows for `γ > 1/8` (and for `γ = 0` from Kahn–Zhao, i.e.
`QuestionTrueZero`).
-/

set_option autoImplicit false

namespace P3CD

open Finset Filter Topology SimpleGraph BackfillPaper3.Challenge P3Basic

theorem two_pow_eq (d m : ℕ) : (2 : ℝ) ^ (2 * d * m) = ((4 : ℝ) ^ d) ^ m := by
  rw [pow_mul, pow_mul]
  norm_num

/-- Exponential decay of the upper tail of `m K_{d,d}` above the mean. -/
theorem upper_decay (d : ℕ) (hd : 1 ≤ d) {x : ℝ} (hx : (d : ℝ) ^ 2 / 4 < x) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ m : ℕ,
      (#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
        (m : ℝ) * x < (edgesIn (KddUnion m d) A : ℝ)) : ℝ) ≤ c ^ m * 2 ^ (2 * d * m) := by
  obtain ⟨q, hq1, hlt⟩ := exists_gt_one_psi_lt d hd hx
  have hq0 : 0 < q := by linarith
  have hP := Pf_pos d hq0.le
  have h4 : (0 : ℝ) < 4 ^ d := by positivity
  refine ⟨Pf d q * q ^ (-x) / 4 ^ d, by positivity, ?_, fun m => ?_⟩
  · rw [div_lt_one h4]
    have hlog : Real.log (Pf d q * q ^ (-x)) < Real.log (4 ^ d) := by
      rw [Real.log_mul hP.ne' (by positivity), Real.log_rpow hq0, Real.log_pow]
      unfold psi at hlt
      rw [Pf_one, Real.log_pow, Real.log_one, mul_zero, sub_zero] at hlt
      linarith
    exact (Real.log_lt_log_iff (by positivity) h4).1 hlog
  · have h := card_gt_markov (KddUnion m d) ((m : ℝ) * x) hq1.le
    rw [evalR_KddUnion] at h
    refine h.trans (le_of_eq ?_)
    rw [show -((m : ℝ) * x) = -x * m by ring, Real.rpow_mul_natCast hq0.le, two_pow_eq,
      div_pow, mul_pow]
    field_simp

/-- `i_γ(m K_{d,d}) = 2^{2dm} - #{A : e(A) > mx}` with `x = 2γd²`. -/
theorem iGamma_KddUnion_split (m d : ℕ) (γ : ℝ) :
    (iGamma (KddUnion m d) d γ : ℝ) = 2 ^ (2 * d * m) -
      #(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
        (m : ℝ) * (2 * γ * (d : ℝ) ^ 2) < (edgesIn (KddUnion m d) A : ℝ)) := by
  have hK := card_le_add_card_gt (KddUnion m d) ((m : ℝ) * (2 * γ * (d : ℝ) ^ 2))
  rw [card_KddUnion] at hK
  rw [iGamma_KddUnion_eq]
  have hK' : ((#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
      (edgesIn (KddUnion m d) A : ℝ) ≤ m * (2 * γ * (d : ℝ) ^ 2)) : ℕ) : ℝ) +
      ((#(univ.filter fun A : Finset (Fin m × (Fin d ⊕ Fin d)) =>
      (m : ℝ) * (2 * γ * (d : ℝ) ^ 2) < (edgesIn (KddUnion m d) A : ℝ)) : ℕ) : ℝ) =
      (2 : ℝ) ^ (2 * d * m) := by
    exact_mod_cast hK
  linarith

theorem iGamma_le_two_pow {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (γ : ℝ) : (iGamma G d γ : ℝ) ≤ 2 ^ Fintype.card V := by
  rw [iGamma_eq_card]
  have h : #(univ.filter fun A : Finset V => (edgesIn G A : ℝ) ≤ γ * d * Fintype.card V) ≤
      2 ^ Fintype.card V := by
    calc _ ≤ #(univ : Finset (Finset V)) := Finset.card_filter_le _ _
      _ = 2 ^ Fintype.card V := by rw [Finset.card_univ, Fintype.card_finset]
  exact_mod_cast h

/-- The decay in the form used below: for `γ > 1/8` and `d ≥ 1` there is `c ∈ (0, 1)` with
`2^{2dm} - i_γ(mK) ≤ c^m 2^{2dm}` for all `m`. -/
theorem decay_KddUnion (d : ℕ) (hd : 1 ≤ d) {γ : ℝ} (hγ : 1 / 8 < γ) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ m : ℕ,
      (2 : ℝ) ^ (2 * d * m) - iGamma (KddUnion m d) d γ ≤ c ^ m * 2 ^ (2 * d * m) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hx : (d : ℝ) ^ 2 / 4 < 2 * γ * (d : ℝ) ^ 2 := by nlinarith [sq_pos_of_pos hdR]
  obtain ⟨c, hc0, hc1, hU⟩ := upper_decay d hd hx
  refine ⟨c, hc0, hc1, fun m => ?_⟩
  rw [iGamma_KddUnion_split]
  have := hU m
  linarith

theorem remark10a : Remark10a := by
  intro d hd γ hγ
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, hc0, hc1, hU⟩ := decay_KddUnion d hd1 hγ
  have hγ0 : 0 ≤ γ := by linarith
  have hiK : ∀ m : ℕ, (1 : ℝ) ≤ iGamma (KddUnion m d) d γ := fun m => by
    exact_mod_cast one_le_iGamma (KddUnion m d) d hγ0
  have hiK2 : ∀ m : ℕ, (iGamma (KddUnion m d) d γ : ℝ) ≤ 2 ^ (2 * d * m) := fun m => by
    have := iGamma_le_two_pow (KddUnion m d) d γ
    rwa [card_KddUnion] at this
  refine ⟨?_, ?_, ?_⟩
  · -- `i_γ(mK) / 2^n → 1`
    have hlow : ∀ m : ℕ, 1 - c ^ m ≤ (iGamma (KddUnion m d) d γ : ℝ) / 2 ^ (2 * d * m) := by
      intro m
      rw [le_div_iff₀ (by positivity)]
      linarith [hU m]
    have hupp : ∀ m : ℕ, (iGamma (KddUnion m d) d γ : ℝ) / 2 ^ (2 * d * m) ≤ 1 := by
      intro m
      rw [div_le_one (by positivity)]
      exact hiK2 m
    have hlim : Tendsto (fun m : ℕ => 1 - c ^ m) atTop (𝓝 1) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1).const_sub 1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hupp
  · -- the relative difference is at most `U(mK)/i_γ(mK)`
    intro a₁ b₁ a₂ b₂ m
    have hG : (iGamma (Gn d m a₁ b₁ a₂ b₂) d γ : ℝ) ≤ 2 ^ (2 * d * m) := by
      have := iGamma_le_two_pow (Gn d m a₁ b₁ a₂ b₂) d γ
      rwa [card_GnV] at this
    have hpos : (0 : ℝ) < iGamma (KddUnion m d) d γ := lt_of_lt_of_le one_pos (hiK m)
    rw [sub_div, div_self hpos.ne']
    exact sub_le_sub_right (div_le_div_of_nonneg_right hG hpos.le) 1
  · -- exponential decay
    refine ⟨1 / (1 - c), c, hc0, hc1, fun m => ?_⟩
    have hpos : (0 : ℝ) < iGamma (KddUnion m d) d γ := lt_of_lt_of_le one_pos (hiK m)
    have h1c : 0 < 1 - c := by linarith
    rw [div_le_iff₀ hpos]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have := hU 0
      simp only [mul_zero, pow_zero, one_mul] at this ⊢
      have h1 : 1 ≤ 1 / (1 - c) := by
        rw [le_div_iff₀ h1c]
        linarith
      nlinarith [hiK 0]
    · have hcm : c ^ m ≤ c := pow_le_of_le_one hc0.le hc1.le hm.ne'
      have h2 : (2 : ℝ) ^ (2 * d * m) * (1 - c) ≤ iGamma (KddUnion m d) d γ := by
        have := hU m
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (2 * d * m)]
      calc (2 : ℝ) ^ (2 * d * m) - iGamma (KddUnion m d) d γ ≤ c ^ m * 2 ^ (2 * d * m) := hU m
        _ = 1 / (1 - c) * c ^ m * ((2 : ℝ) ^ (2 * d * m) * (1 - c)) := by
          field_simp
        _ ≤ 1 / (1 - c) * c ^ m * iGamma (KddUnion m d) d γ :=
          mul_le_mul_of_nonneg_left h2 (by positivity)

theorem readingR6 (hQ : QuestionTrueZero) : ReadingR6 := by
  intro d hd γ hγ ε hε
  rcases hγ with rfl | hγ
  · refine ⟨1, fun m hm V _ _ G _ hV hG => ?_⟩
    have hadm : Admissible (2 * d * m) d :=
      ⟨hd, Nat.one_le_iff_ne_zero.2 (by positivity), Dvd.intro m rfl⟩
    have h := hQ (2 * d * m) d hadm V G hV hG
    rw [Nat.mul_div_cancel_left m (by omega : 0 < 2 * d)] at h
    have h' : (iGamma G d 0 : ℝ) ≤ iGamma (KddUnion m d) d 0 := by exact_mod_cast h
    have h0 : (0 : ℝ) ≤ iGamma (KddUnion m d) d 0 := Nat.cast_nonneg _
    nlinarith
  · obtain ⟨c, hc0, hc1, hU⟩ := decay_KddUnion d hd hγ
    obtain ⟨M₀, hM₀⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (1 + ε) by positivity) hc1
    refine ⟨M₀, fun m hm V _ _ G _ hV hG => ?_⟩
    have hcm : c ^ m ≤ ε / (1 + ε) := (pow_le_pow_of_le_one hc0.le hc1.le hm).trans hM₀.le
    have hGle : (iGamma G d γ : ℝ) ≤ 2 ^ (2 * d * m) := by
      have := iGamma_le_two_pow G d γ
      rwa [hV] at this
    have hK := hU m
    have h2 : (0 : ℝ) < 2 ^ (2 * d * m) := by positivity
    have h3 : (2 : ℝ) ^ (2 * d * m) ≤ (1 + ε) * iGamma (KddUnion m d) d γ := by
      have h4 : c ^ m * (1 + ε) ≤ ε := by
        rw [le_div_iff₀ (by positivity)] at hcm
        exact hcm
      nlinarith
    linarith

end P3CD
