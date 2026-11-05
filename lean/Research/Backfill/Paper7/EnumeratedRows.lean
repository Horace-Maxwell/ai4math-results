import Research.Backfill.Paper7.LegacyEnumeration

/-! Uncompiled Root candidate: exact list-level coverage of the frozen budget
recursion, including zero rows and zero budget. This is not a main check. -/

set_option autoImplicit false
noncomputable section

namespace Paper7Pruning
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

def rowWeight (row : List (ℕ × ℕ)) : ℕ :=
  (row.map (fun a => a.1 + 2 * a.2)).sum
#print axioms Paper7Pruning.rowWeight

theorem rowWeight_nil : rowWeight [] = 0 := rfl
#print axioms Paper7Pruning.rowWeight_nil

theorem rowWeight_cons (p q : ℕ) (tail : List (ℕ × ℕ)) :
    rowWeight ((p, q) :: tail) = p + 2 * q + rowWeight tail := rfl
#print axioms Paper7Pruning.rowWeight_cons

theorem mem_enumerateRows_iff (r W : ℕ) (row : List (ℕ × ℕ)) :
    row ∈ enumerateRows r W ↔ row.length = r ∧ rowWeight row ≤ W := by
  induction r generalizing W row with
  | zero =>
    constructor
    · intro h
      have he : row = [] := by simpa [enumerateRows] using h
      subst row
      simp [rowWeight]
    · rintro ⟨hlen, _⟩
      have he : row = [] := List.length_eq_zero_iff.mp hlen
      subst row
      simp [enumerateRows]
  | succ r ih =>
    constructor
    · intro h
      rcases List.mem_flatMap.mp h with ⟨p, hp, h⟩
      rcases List.mem_flatMap.mp h with ⟨q, hq, h⟩
      rcases List.mem_map.mp h with ⟨tail, ht, he⟩
      subst row
      obtain ⟨hlen, hweight⟩ := (ih (W - p - 2 * q) tail).mp ht
      have hp' := List.mem_range.mp hp
      have hq' := List.mem_range.mp hq
      constructor
      · simp only [List.length_cons, hlen]
      · rw [rowWeight_cons]
        omega
    · rintro ⟨hlen, hweight⟩
      cases row with
      | nil => simp at hlen
      | cons a tail =>
        rcases a with ⟨p, q⟩
        have htail : tail.length = r := by simpa using hlen
        rw [rowWeight_cons] at hweight
        have hp : p ∈ List.range (W + 1) := List.mem_range.mpr (by omega)
        have hq : q ∈ List.range ((W - p) / 2 + 1) :=
          List.mem_range.mpr (by omega)
        have ht : tail ∈ enumerateRows r (W - p - 2 * q) :=
          (ih (W - p - 2 * q) tail).mpr ⟨htail, by omega⟩
        exact List.mem_flatMap.mpr ⟨p, hp,
          List.mem_flatMap.mpr ⟨q, hq, List.mem_map.mpr ⟨tail, ht, rfl⟩⟩⟩
#print axioms Paper7Pruning.mem_enumerateRows_iff

end Paper7Pruning
