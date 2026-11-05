import Research.Backfill.Paper7.PathBlockResolvent

set_option autoImplicit false

noncomputable section

namespace Paper7Reduced

open scoped Matrix

/-- The original shifted path equation, with forcing at the first vertex. -/
def pathEquation (x : ℚ) (t : ℕ) (f : Fin t → ℚ) (y : ℚ) : Prop :=
  ∀ a, (Paper7Cleared.pathShift x t *ᵥ f) a -
    (if a.val = 0 then y else 0) = 0

#print axioms Paper7Reduced.pathEquation

theorem pathEquation_one_iff (x : ℚ) (f : Fin 1 → ℚ) (y : ℚ) :
    pathEquation x 1 f y ↔ x * f 0 - y = 0 := by
  unfold pathEquation
  rw [Fin.forall_fin_one]
  norm_num [Paper7Cleared.pathShift, Matrix.mulVec, dotProduct]

#print axioms Paper7Reduced.pathEquation_one_iff

theorem pathEquation_two_iff (x : ℚ) (f : Fin 2 → ℚ) (y : ℚ) :
    pathEquation x 2 f y ↔
      (x * f 0 - f 1 - y = 0 ∧ x * f 1 - f 0 = 0) := by
  unfold pathEquation
  rw [Fin.forall_fin_two]
  norm_num [Paper7Cleared.pathShift, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, sub_eq_add_neg, add_comm]

#print axioms Paper7Reduced.pathEquation_two_iff

/-- Full pointwise classification at zero, including both converse directions. -/
theorem zero_path_iff (t : ℕ) (ht : t = 1 ∨ t = 2)
    (a0 : Fin t) (ha0 : a0.val = 0) (f : Fin t → ℚ) (y : ℚ) :
    pathEquation 0 t f y ↔
      ((t = 1 → y = 0) ∧ ∀ a, f a =
        if t = 1 then f a0 else if a.val = 0 then 0 else -y) := by
  rcases ht with rfl | rfl
  · rw [pathEquation_one_iff]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro _
        linarith
      · intro a
        have ha : a = a0 := Subsingleton.elim _ _
        simp [ha]
    · rintro ⟨hy, _⟩
      simp [hy rfl]
  · have ha : a0 = 0 := Fin.ext ha0
    subst a0
    rw [pathEquation_two_iff]
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨by omega, ?_⟩
      intro a
      fin_cases a
      · norm_num
        linarith
      · norm_num
        linarith
    · rintro ⟨_, hf⟩
      have hf0 : f 0 = 0 := by simpa using hf 0
      have hf1 : f 1 = -y := by simpa using hf 1
      simp [hf0, hf1]

#print axioms Paper7Reduced.zero_path_iff

/-- Full pointwise classification at either rational root of x² = 1. -/
theorem sign_path_iff (ε : ℚ) (he : ε ^ 2 = 1)
    (t : ℕ) (ht : t = 1 ∨ t = 2)
    (a0 : Fin t) (ha0 : a0.val = 0) (f : Fin t → ℚ) (y : ℚ) :
    pathEquation ε t f y ↔
      ((t = 2 → y = 0) ∧ ∀ a, f a =
        if t = 1 then ε * y else if a.val = 0 then f a0 else ε * f a0) := by
  have hec (z : ℚ) : ε * (ε * z) = z := by
    rw [← mul_assoc, ← pow_two, he, one_mul]
  rcases ht with rfl | rfl
  · rw [pathEquation_one_iff]
    constructor
    · intro h
      have hf0 : f 0 = ε * y := by
        simpa only [hec] using
          congrArg (fun z : ℚ => ε * z) (sub_eq_zero.mp h)
      refine ⟨by omega, ?_⟩
      intro a
      have ha : a = 0 := Subsingleton.elim _ _
      simpa [ha] using hf0
    · rintro ⟨_, hf⟩
      have hf0 : f 0 = ε * y := by simpa using hf 0
      rw [hf0, hec, sub_self]
  · have ha : a0 = 0 := Fin.ext ha0
    subst a0
    rw [pathEquation_two_iff]
    constructor
    · rintro ⟨h0, h1⟩
      have hf1 : f 1 = ε * f 0 := by
        simpa only [hec] using
          congrArg (fun z : ℚ => ε * z) (sub_eq_zero.mp h1)
      have hy : y = 0 := by
        rw [hf1] at h0
        linarith
      refine ⟨fun _ => hy, ?_⟩
      intro a
      fin_cases a
      · simp
      · simpa using hf1
    · rintro ⟨hy, hf⟩
      have hy0 : y = 0 := hy rfl
      have hf1 : f 1 = ε * f 0 := by simpa using hf 1
      constructor
      · rw [hf1, hy0]
        ring
      · rw [hf1, hec, sub_self]

#print axioms Paper7Reduced.sign_path_iff

/-- Every permitted free value produces a solution at zero. -/
theorem zero_path_lift (t : ℕ) (ht : t = 1 ∨ t = 2)
    (a0 : Fin t) (ha0 : a0.val = 0) (y z : ℚ) (hy : t = 1 → y = 0) :
    pathEquation 0 t
      (fun a => if t = 1 then z else if a.val = 0 then 0 else -y) y := by
  apply (zero_path_iff t ht a0 ha0 _ y).2
  refine ⟨hy, ?_⟩
  intro a
  by_cases h1 : t = 1
  · simp [h1]
  · simp [h1]

#print axioms Paper7Reduced.zero_path_lift

/-- Every permitted free value produces a solution at either sign. -/
theorem sign_path_lift (ε : ℚ) (he : ε ^ 2 = 1)
    (t : ℕ) (ht : t = 1 ∨ t = 2)
    (a0 : Fin t) (ha0 : a0.val = 0) (y z : ℚ) (hy : t = 2 → y = 0) :
    pathEquation ε t
      (fun a => if t = 1 then ε * y else if a.val = 0 then z else ε * z) y := by
  apply (sign_path_iff ε he t ht a0 ha0 _ y).2
  refine ⟨hy, ?_⟩
  intro a
  by_cases h1 : t = 1
  · simp [h1]
  · simp [h1, ha0]

#print axioms Paper7Reduced.sign_path_lift

end Paper7Reduced
