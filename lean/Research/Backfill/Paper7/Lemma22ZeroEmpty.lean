import Research.Backfill.Paper7.Lemma22MaximumBounds

/-! Exact zero multiplicity for empty Kp, with the frozen 4-divisibility test.
The nonempty-support even-gap count remains a separate missing construction. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Lemma22Gaps
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Lemma22Periodic

theorem monodromy_constant (b : ℕ) (a : ℝ) :
    monodromy b (fun _ => a) = transfer a ^ b := by
  simp only [monodromy, List.map_const', List.length_reverse,
    List.length_finRange, List.prod_replicate]
#print axioms Paper7Lemma22Gaps.monodromy_constant

theorem transfer_zero_pow_four : (transfer 0) ^ 4 = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transfer, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
#print axioms Paper7Lemma22Gaps.transfer_zero_pow_four

theorem zero_transfer_fixed_finrank (b : ℕ) :
    Module.finrank ℝ (fixedSpace b (fun _ => 0)) = if 4 ∣ b then 2 else 0 := by
  have hm : monodromy b (fun _ => 0) = transfer 0 ^ (b % 4) :=
    (monodromy_constant b 0).trans (pow_eq_pow_mod b transfer_zero_pow_four)
  calc
    Module.finrank ℝ (fixedSpace b (fun _ => 0)) =
        Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (transfer 0 ^ (b % 4) - 1))) :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
        Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (M - 1)))) hm
    _ = if 4 ∣ b then 2 else 0 := by
      by_cases hd : 4 ∣ b
      · rw [ite_eq_left hd]
        have hf : Matrix.toLin' (transfer 0 ^ (b % 4) - 1) = 0 := by
          rw [Nat.mod_eq_zero_of_dvd hd, pow_zero, sub_self, map_zero]
        have hk : LinearMap.ker (Matrix.toLin' (transfer 0 ^ (b % 4) - 1)) = ⊤ := by
          rw [hf, LinearMap.ker_zero]
        calc
          _ = Module.finrank ℝ (⊤ : Submodule ℝ (Fin 2 → ℝ)) :=
            (LinearEquiv.ofEq _ _ hk).finrank_eq
          _ = 2 := by simp only [finrank_top, Module.finrank_fin_fun]
      · rw [ite_eq_right hd]
        have hr : b % 4 < 4 := Nat.mod_lt b (by decide)
        have hn : b % 4 ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
        have hdet : (transfer 0 ^ (b % 4) - 1).det ≠ 0 := by
          rcases (show b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 by omega) with he | he | he <;>
            rw [he] <;>
            norm_num [transfer, Matrix.det_fin_two, Matrix.sub_apply,
              Matrix.one_apply, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        have hbot : LinearMap.ker (Matrix.toLin' (transfer 0 ^ (b % 4) - 1)) = ⊥ := by
          by_contra hne
          have hz := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne
          rw [LinearMap.det_toLin'] at hz
          exact hdet hz
        calc
          _ = Module.finrank ℝ (⊥ : Submodule ℝ (Fin 2 → ℝ)) :=
            (LinearEquiv.ofEq _ _ hbot).finrank_eq
          _ = 0 := finrank_bot ℝ (Fin 2 → ℝ)

#print axioms Paper7Lemma22Gaps.zero_transfer_fixed_finrank

theorem zero_nullity_empty_support (b : ℕ) (p : Fin b → ℕ) (hb : 3 ≤ b)
    (hK : Kp b p = ∅) :
    matrixNullity (overQ (zeroSystem b p)) = if 4 ∣ b then 2 else 0 := by
  have hKq : Kq b p = ∅ := hK
  calc
    matrixNullity (overQ (zeroSystem b p)) = deltaE b (fun _ => 0) p 0 :=
      zero_nullity_eq_deltaE_zero b p hb
    _ = Module.finrank ℝ (fixedSpace b (fun _ => 0)) := by
      have hc : (fun _ : Fin b => (0 : ℝ) * (1 - ((0 : ℕ) : ℝ))) =
          (fun _ : Fin b => (0 : ℝ)) := by
        funext k
        exact zero_mul _
      have hs := congrArg (fixedSpace b) hc
      exact (wmatKernelEquivFixedOfEmpty b (fun _ => 0) p hb 0 hKq).finrank_eq.trans
        (LinearEquiv.ofEq _ _ hs).finrank_eq
    _ = if 4 ∣ b then 2 else 0 := zero_transfer_fixed_finrank b
#print axioms Paper7Lemma22Gaps.zero_nullity_empty_support

/-- The exact frozen zero-offset formula on the empty-support branch. -/
theorem lemma22_zero_empty_clause (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hK : Kp b p = ∅) :
    mult (SG b p q) 0 + (Kp b p).card = ∑ k, p k + delta0 b p := by
  have h := Paper7Lemma22.zero_offset_reduced b p q hb
  rw [zero_nullity_empty_support b p hb hK] at h
  simpa only [delta0, hK, ite_true] using h
#print axioms Paper7Lemma22Gaps.lemma22_zero_empty_clause

end Paper7Lemma22Gaps
