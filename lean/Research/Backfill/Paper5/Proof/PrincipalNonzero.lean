import Research.Backfill.Paper5.Proof.ReesBasic

set_option autoImplicit false

namespace CodexPaper5.PrincipalNonzero

open BackfillPaper5 Function

/-- Restrict the two actual principal-factor bijections to the nonzero part.
The product's membership in the original subset is proved from its nonzero image.
No finiteness or associativity is required. -/
theorem subsetHasCM_of_pfHasCM {S : Type} (op : S → S → S) (J : Set S)
    [DecidablePred (· ∈ J)] (hcm : Challenge.PFHasCM op J) :
    Challenge.SubsetHasCM op J := by
  classical
  obtain ⟨α, hα⟩ := hcm
  have hzero : α none = none :=
    CodexPaper5.check_ZeroFixed (Option J) (Challenge.pfMul op J) none
      (fun x => ⟨by cases x <;> rfl, by cases x <;> rfl⟩) α hα
  have hαsome : ∀ x : J, ∃ y : J, α (some x) = some y := by
    intro x
    cases h : α (some x) with
    | none =>
        have hx : some x = none := hα.1.1 (h.trans hzero.symm)
        cases hx
    | some y => exact ⟨y, rfl⟩
  choose β hβ using hαsome
  have hβinj : Injective β := by
    intro x y h
    apply Option.some.inj
    apply hα.1.1
    rw [hβ x, hβ y, h]
  have hβsurj : Surjective β := by
    intro y
    obtain ⟨w, hw⟩ := hα.1.2 (some y)
    cases w with
    | none =>
        rw [hzero] at hw
        cases hw
    | some x => exact ⟨x, Option.some.inj ((hβ x).symm.trans hw)⟩
  have hnonzero : ∀ x : J,
      Challenge.pfMul op J (some x) (α (some x)) ≠ none := by
    intro x h
    have hz : Challenge.pfMul op J none (α none) = none := rfl
    have hx : some x = none := hα.2.1 (h.trans hz.symm)
    cases hx
  have hmem : ∀ x : J, op x (β x) ∈ J := by
    intro x
    by_contra h
    apply hnonzero x
    rw [hβ x]
    simp only [Challenge.pfMul, dite_eq_right h]
  let θ : J → J := fun x => ⟨op x (β x), hmem x⟩
  have hθ : ∀ x : J,
      Challenge.pfMul op J (some x) (α (some x)) = some (θ x) := by
    intro x
    rw [hβ x]
    simp only [Challenge.pfMul, dite_eq_left (hmem x), θ]
  have hθinj : Injective θ := by
    intro x y h
    apply Option.some.inj
    apply hα.2.1
    change Challenge.pfMul op J (some x) (α (some x)) =
      Challenge.pfMul op J (some y) (α (some y))
    rw [hθ x, hθ y, h]
  have hθsurj : Surjective θ := by
    intro y
    obtain ⟨w, hw⟩ := hα.2.2 (some y)
    cases w with
    | none =>
        change none = some y at hw
        cases hw
    | some x => exact ⟨x, Option.some.inj ((hθ x).symm.trans hw)⟩
  exact ⟨β, ⟨hβinj, hβsurj⟩, hmem, ⟨hθinj, hθsurj⟩⟩

#print axioms CodexPaper5.PrincipalNonzero.subsetHasCM_of_pfHasCM

end CodexPaper5.PrincipalNonzero
