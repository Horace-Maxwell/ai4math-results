import Research.Backfill.Paper7.Lemma22RealReduction

/-! Complete 2-by-2 kernel classification. This does not yet identify the Sun
multiplicity with this kernel: that separate periodic-recurrence bridge is open. -/
set_option autoImplicit false
noncomputable section

namespace Paper7Lemma22
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem two_by_two_kernel_classification (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hdet : M.det = 1) :
    matrixNullity (M - 1) ≤ 2 ∧
    (matrixNullity (M - 1) = 2 ↔ M = 1) ∧
    (matrixNullity (M - 1) = 1 ↔ M ≠ 1 ∧ M.trace = 2) := by
  let f := Matrix.toLin' (M - 1)
  let k := Module.finrank ℝ (LinearMap.ker f)
  change k ≤ 2 ∧ (k = 2 ↔ M = 1) ∧ (k = 1 ↔ M ≠ 1 ∧ M.trace = 2)
  have hle : k ≤ 2 := by
    simpa only [k, Module.finrank_fin_fun] using (LinearMap.ker f).finrank_le
  have htwo : k = 2 ↔ M = 1 := by
    constructor
    · intro hk
      have htop : LinearMap.ker f = ⊤ :=
        Submodule.eq_top_of_finrank_eq
          (by simpa only [k, Module.finrank_fin_fun] using hk)
      have hz : M - 1 = 0 := by
        apply Matrix.toLin'.injective
        simpa only [f, map_zero] using (LinearMap.ker_eq_top.mp htop)
      exact sub_eq_zero.mp hz
    · intro hM
      have hz : f = 0 := by
        dsimp [f]
        rw [hM, sub_self, map_zero]
      change Module.finrank ℝ (LinearMap.ker f) = 2
      rw [hz, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun]
  have hd : (M - 1).det = 2 - M.trace := by
    have h := hdet
    rw [Matrix.det_fin_two] at h
    norm_num [Matrix.det_fin_two, Matrix.trace_fin_two,
      Matrix.sub_apply, Matrix.one_apply]
    nlinarith [h]
  have hnonzero : k ≠ 0 ↔ M.trace = 2 := by
    calc
      k ≠ 0 ↔ LinearMap.ker f ≠ ⊥ :=
        not_congr (Submodule.finrank_eq_zero (S := LinearMap.ker f))
      _ ↔ f.det = 0 := LinearMap.det_eq_zero_iff_ker_ne_bot.symm
      _ ↔ M.trace = 2 := by
        simp only [f, LinearMap.det_toLin', hd]
        constructor <;> intro h <;> linarith
  refine ⟨hle, htwo, ?_⟩
  constructor
  · intro hk
    refine ⟨?_, hnonzero.mp (by omega)⟩
    intro hM
    have := htwo.mpr hM
    omega
  · rintro ⟨hM, ht⟩
    have hk0 := hnonzero.mpr ht
    have hk2 : k ≠ 2 := fun hk => hM (htwo.mp hk)
    omega

#print axioms Paper7Lemma22.two_by_two_kernel_classification

theorem monodromy_kernel_classification (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) :
    matrixNullity (Mono b p q m - 1) ≤ 2 ∧
    (matrixNullity (Mono b p q m - 1) = 2 ↔ Mono b p q m = 1) ∧
    (matrixNullity (Mono b p q m - 1) = 1 ↔
      Mono b p q m ≠ 1 ∧ (Mono b p q m).trace = 2) :=
  two_by_two_kernel_classification _ (monodromy_det_one b p q m)

#print axioms Paper7Lemma22.monodromy_kernel_classification

end Paper7Lemma22
