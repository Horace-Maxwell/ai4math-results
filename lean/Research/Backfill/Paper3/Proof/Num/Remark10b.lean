import Research.Backfill.Paper3.Proof.Num.RunR10b

/-!
# Remark 10(b)

For `d = 2`, `γ = 1/4`, `n = 400` (`m = 100`, threshold `200`): the prefix sums computed in
`run_R10b` are `i_γ(m K_{2,2})` and `i_γ(G_n)` (`runSt_spec`, `iGamma_KddUnion`, `iGamma_Gn`),
and the two checked inequalities `(10^19 + 125) a ≤ 10^19 g < (10^19 + 135) a` give
`g/a − 1 ∈ [1.25·10^{-17}, 1.35·10^{-17})`.
-/

set_option autoImplicit false

namespace P3Num

open Finset Polynomial BackfillPaper3.Challenge

theorem r10b_A : sumL (takeL 201 (runSt K2 H2 201 (fun _ => []) 100).A) =
    iGamma (KddUnion 100 2) 2 (1 / 4) := by
  have hA := (runSt_spec K2 H2 201 (fun _ => []) 100).1
  rw [iGamma_KddUnion 100 2 1 4 (1 / 4) (by norm_num), Pd_two,
    show 1 * 2 * (2 * 2 * 100) / 4 = 200 by norm_num]
  exact sumL_takeL_eq_prefN hA (by norm_num)

theorem r10b_B (a₁ b₁ a₂ b₂ : Fin 2) : sumL (takeL 201 (runSt K2 H2 201 (fun _ => []) 100).B) =
    iGamma (Gn 2 100 a₁ b₁ a₂ b₂) 2 (1 / 4) := by
  have hB := (runSt_spec K2 H2 201 (fun _ => []) 100).2.1
  rw [iGamma_Gn 2 100 a₁ b₁ a₂ b₂ 1 4 (1 / 4) (by norm_num), edgePoly_H2, Pd_two,
    show 1 * 2 * (2 * 2 * 100) / 4 = 200 by norm_num, show (100 : ℕ) % 2 = 0 from rfl, pow_zero,
    mul_one]
  exact sumL_takeL_eq_prefN hB (by norm_num)

theorem r10b_nat (a₁ b₁ a₂ b₂ : Fin 2) :
    (10 ^ 19 + 125) * iGamma (KddUnion 100 2) 2 (1 / 4) ≤
        10 ^ 19 * iGamma (Gn 2 100 a₁ b₁ a₂ b₂) 2 (1 / 4) ∧
      10 ^ 19 * iGamma (Gn 2 100 a₁ b₁ a₂ b₂) 2 (1 / 4) <
        (10 ^ 19 + 135) * iGamma (KddUnion 100 2) 2 (1 / 4) := by
  have h := run_R10b
  rw [r10bOK, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, r10b_A, r10b_B a₁ b₁ a₂ b₂] at h
  exact h

theorem remark10b : Remark10b := by
  obtain ⟨h1, h2⟩ := r10b_nat 0 0 0 0
  set a := iGamma (KddUnion 100 2) 2 (1 / 4)
  set g := iGamma (Gn 2 100 0 0 0 0) 2 (1 / 4)
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, mul_zero] at h2
      exact absurd h2 (Nat.not_lt_zero _)
    · exact h0
  have ha : (0 : ℝ) < a := by exact_mod_cast ha0
  have h1R : ((10 : ℝ) ^ 19 + 125) * a ≤ 10 ^ 19 * g := by exact_mod_cast h1
  have h2R : (10 : ℝ) ^ 19 * g < (10 ^ 19 + 135) * a := by exact_mod_cast h2
  constructor
  · rw [div_sub_one ha.ne', le_div_iff₀ ha]
    have hp : (0 : ℝ) < 10 ^ 19 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]
    linarith
  · rw [div_sub_one ha.ne', div_lt_iff₀ ha]
    have hp : (0 : ℝ) < 10 ^ 19 := by positivity
    rw [div_mul_eq_mul_div, lt_div_iff₀ hp]
    linarith

end P3Num
