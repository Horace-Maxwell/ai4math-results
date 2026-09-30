import Research.Backfill.Paper8.Proof.Spec.Eigen

/-!
# Paper 8, Lemma 3.1(iii): the kernel of `A(T(a))`

For `θ = 0` the equations (3.1) say `∑_i x_{v_i} = 0`, `x_c + ∑_{ℓ ∈ L_i} x_ℓ = 0` for every `i`
and `x_{v_i} = 0` when `a_i ≥ 1` (`mulVec_eq_zero_iff`). A bare branch forces `x_c = 0`
(`lemma_3_1_iii`).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix

namespace P8Spec

variable {k : ℕ} (a : Fin k → ℕ)

/-- `A x = 0`, coordinatewise. -/
theorem mulVec_eq_zero_iff (x : TV a → ℝ) :
    adjT a *ᵥ x = 0 ↔
      (∑ i, x (some ⟨i, none⟩) = 0 ∧
        (∀ i, x none + ∑ j, x (some ⟨i, some j⟩) = 0) ∧
        (∀ i, 1 ≤ a i → x (some ⟨i, none⟩) = 0)) := by
  have h0 : adjT a *ᵥ x = 0 ↔ adjT a *ᵥ x = (0 : ℝ) • x := by rw [zero_smul]
  rw [h0, P8Basic.mulVec_eq_smul_iff]
  simp only [zero_mul]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, fun i => (h2 i).symm, fun i hi => (h3 i ⟨0, hi⟩).symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, fun i => (h2 i).symm, fun i j => (h3 i (by have := j.isLt; omega)).symm⟩

/-- The leaf sum of a bare branch is `0`. -/
theorem sum_bare (x : TV a → ℝ) (i : Fin k) (hi : a i = 0) :
    ∑ j, x (some ⟨i, some j⟩) = 0 :=
  Finset.sum_eq_zero (fun j _ => absurd j.isLt (by omega))

theorem exists_bare_of_kb (hk0 : 1 ≤ kb (branchMS a) 0) : ∃ i, a i = 0 := by
  rw [kb_branchMS] at hk0
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hk0
  exact ⟨i, by simpa [Ib] using hi⟩

theorem one_le_of_kb_zero (hk0 : kb (branchMS a) 0 = 0) (i : Fin k) : 1 ≤ a i := by
  by_contra h
  have hi : a i = 0 := by omega
  have : 0 < kb (branchMS a) 0 := by
    rw [kb_branchMS]
    exact Finset.card_pos.2 ⟨i, by simp [Ib, hi]⟩
  omega

/-- Lemma 3.1(iii). -/
theorem lemma_3_1_iii :
    (1 ≤ kb (branchMS a) 0 → ∀ x : TV a → ℝ, adjT a *ᵥ x = 0 ↔
      (x none = 0 ∧
        (∀ i, 1 ≤ a i → x (some ⟨i, none⟩) = 0 ∧ ∑ j, x (some ⟨i, some j⟩) = 0) ∧
        ∑ i ∈ Ib a 0, x (some ⟨i, none⟩) = 0)) ∧
    (kb (branchMS a) 0 = 0 → ∀ x : TV a → ℝ, adjT a *ᵥ x = 0 ↔
      ∀ i, x (some ⟨i, none⟩) = 0 ∧ ∑ j, x (some ⟨i, some j⟩) = -x none) := by
  constructor
  · intro hk0 x
    obtain ⟨i0, hi0⟩ := exists_bare_of_kb a hk0
    rw [mulVec_eq_zero_iff]
    have hsub : ∀ f : Fin k → ℝ, (∀ i, 1 ≤ a i → f i = 0) → ∑ i ∈ Ib a 0, f i = ∑ i, f i := by
      intro f hf
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      apply hf i
      simp only [Ib, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      omega
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hc : x none = 0 := by
        have e := h2 i0
        rwa [sum_bare a x i0 hi0, add_zero] at e
      refine ⟨hc, fun i hi => ⟨h3 i hi, ?_⟩, ?_⟩
      · have e := h2 i
        rwa [hc, zero_add] at e
      · rw [hsub _ h3, h1]
    · rintro ⟨hc, h2, hsum⟩
      refine ⟨?_, fun i => ?_, fun i hi => (h2 i hi).1⟩
      · rw [← hsub _ (fun i hi => (h2 i hi).1), hsum]
      · rw [hc, zero_add]
        by_cases hi : 1 ≤ a i
        · exact (h2 i hi).2
        · exact sum_bare a x i (by omega)
  · intro hk0 x
    have hall := one_le_of_kb_zero a hk0
    rw [mulVec_eq_zero_iff]
    constructor
    · rintro ⟨_, h2, h3⟩ i
      refine ⟨h3 i (hall i), ?_⟩
      have e := h2 i
      linarith
    · intro h
      refine ⟨Finset.sum_eq_zero (fun i _ => (h i).1), fun i => ?_, fun i _ => (h i).1⟩
      rw [(h i).2]
      ring

end P8Spec
