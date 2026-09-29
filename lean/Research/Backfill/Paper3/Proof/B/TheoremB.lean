import Research.Backfill.Paper3.Proof.B.Totals

/-!
# Theorem B and `Neg_2d`

`S_d` is `d`-regular (a valid 2-switch of `K_{d,d}`), the inclusion and the counts come from
`Research.Backfill.Paper3.Proof.B.Totals`, and for `n = 2d`, `γ ∈ [1/(2d²), 1/d²)` we have `⌊γ d n⌋ = 1`, so
`i_γ(S_d) = N_{≤1}(S_d) > N_{≤1}(K_{d,d}) = i_γ(K_{d,d})`.
-/

set_option autoImplicit false

namespace P3B

open Finset SimpleGraph BackfillPaper3.Challenge

section

variable {d : ℕ} {a₁ a₂ b₁ b₂ : Fin d}

theorem sd_regular (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) : (Sd d a₁ a₂ b₁ b₂).IsRegularOfDegree d :=
  (sd_valid ha hb).isRegularOfDegree (kdd_regular d)

theorem sd_inclusion (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) (A : Finset (Fin d ⊕ Fin d))
    (h : edgesIn (Kdd d) A ≤ 1) : edgesIn (Sd d a₁ a₂ b₁ b₂) A ≤ 1 := by
  obtain ⟨S, T, rfl⟩ : ∃ S T : Finset (Fin d), A = S.disjSum T :=
    ⟨A.toLeft, A.toRight, Finset.toLeft_disjSum_toRight.symm⟩
  rw [P3Basic.edgesIn_Kdd] at h
  exact sd_le_one_of_kdd ha hb S T h

/-- `i_γ` of `m K_{d,d}` with `m = 1` is `i_γ` of `K_{d,d}`. -/
theorem iGamma_kddUnion_one {m : ℕ} (hm : m = 1) {γ : ℝ} (hγ : 0 ≤ γ) :
    iGamma (KddUnion m d) d γ = iGamma (Kdd d) d γ := by
  subst hm
  exact P3Basic.iGamma_iso (kddUnionOneIso d) d hγ

theorem card_sum_fin (d : ℕ) : Fintype.card (Fin d ⊕ Fin d) = 2 * d := by
  rw [Fintype.card_sum, Fintype.card_fin]
  ring

/-- For `γ ∈ [1/(2d²), 1/d²)`, `⌊γ · d · 2d⌋ = 1`. -/
theorem floor_two_d (hd : 1 ≤ d) {γ : ℝ} (h1 : 1 / (2 * (d : ℝ) ^ 2) ≤ γ)
    (h2 : γ < 1 / (d : ℝ) ^ 2) : ⌊γ * d * ((2 * d : ℕ) : ℝ)⌋₊ = 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have e1 : 1 ≤ γ * (2 * (d : ℝ) ^ 2) := (div_le_iff₀ (by positivity)).mp h1
  have e2 : γ * (d : ℝ) ^ 2 < 1 := (lt_div_iff₀ (by positivity)).mp h2
  have hγ : 0 ≤ γ := le_trans (by positivity) h1
  rw [Nat.floor_eq_iff (by positivity)]
  push_cast
  constructor <;> nlinarith

/-- The last assertion of Theorem B. -/
theorem sd_not_question (hd : 3 ≤ d) (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) {γ : ℝ}
    (h1 : 1 / (2 * (d : ℝ) ^ 2) ≤ γ) (h2 : γ < 1 / (d : ℝ) ^ 2) :
    ¬ CareniniQuestion (2 * d) d γ := by
  intro hQ
  have hγ : 0 ≤ γ := le_trans (by positivity) h1
  have hle := hQ (Fin d ⊕ Fin d) (Sd d a₁ a₂ b₁ b₂) (card_sum_fin d) (sd_regular ha hb)
  rw [iGamma_kddUnion_one (Nat.div_self (by omega)) hγ, P3Basic.iGamma_eq_iCount_floor _ _ hγ,
    P3Basic.iGamma_eq_iCount_floor _ _ hγ, card_sum_fin d, floor_two_d (by omega) h1 h2,
    iCount_sd_one ha hb] at hle
  omega

theorem iCount_sd_one_int (hd : 3 ≤ d) (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) :
    (iCount (Sd d a₁ a₂ b₁ b₂) 1 : ℤ) = 2 ^ (d + 1) + (d : ℤ) ^ 2 + 4 * d - 9 := by
  rw [iCount_sd_one ha hb, iCount_kdd_one]
  have hP : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
  have e1 : ((2 ^ (d + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (d + 1) := by push_cast; ring
  have e2 : ((d ^ 2 : ℕ) : ℤ) = (d : ℤ) ^ 2 := by push_cast; ring
  rw [← e1, ← e2]
  generalize 2 ^ (d + 1) = P at hP ⊢
  generalize d ^ 2 = Q
  omega

end

theorem theoremB : TheoremB := by
  intro d hd a₁ a₂ b₁ b₂ ha hb
  refine ⟨sd_regular ha hb, fun A hA => sd_inclusion ha hb A hA, ?_, iCount_sd_one_int hd ha hb,
    fun γ h1 h2 => sd_not_question hd ha hb h1 h2⟩
  rw [iCount_sd_one ha hb]
  omega

theorem neg_2d : Neg_2d := by
  intro d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine sd_not_question (a₁ := ⟨0, by omega⟩) (a₂ := ⟨1, by omega⟩) (b₁ := ⟨0, by omega⟩)
    (b₂ := ⟨1, by omega⟩) hd (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) le_rfl ?_
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith

end P3B
