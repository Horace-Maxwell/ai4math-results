import Research.TaskP.GradedWilf.Challenge

namespace TaskP.GradedWilf
open Challenge

theorem degree_add {d : ℕ} (x y : Point d) : degree (x+y) = degree x + degree y := by
  simp [degree, Finset.sum_add_distrib]

theorem degree_zero_iff {d : ℕ} (x : Point d) : degree x = 0 ↔ x = 0 := by
  simp [degree, Finset.sum_eq_zero_iff, funext_iff]

def semigroup (a b d : ℕ) : AddSubmonoid (Point d) where
  carrier := graded a b d
  zero_mem' := by simp [graded, degree]
  add_mem' := by
    intro x y hx hy
    change degree (x + y) ∈ scalar a b
    rw [degree_add]
    exact (scalar a b).add_mem hx hy

theorem atoms_generate (a b d : ℕ) :
    (AddSubmonoid.closure (atoms (graded a b d)) : Set (Point d)) = graded a b d := by
  let S := semigroup a b d
  let A := atoms (graded a b d)
  apply Set.Subset.antisymm
  · exact (show AddSubmonoid.closure A ≤ S from AddSubmonoid.closure_le.2 (fun _ h => h.1))
  intro x hx
  change x ∈ AddSubmonoid.closure A
  induction hn : degree x using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases h0 : x = 0
    · simp [h0]
    by_cases ha : x ∈ A
    · exact AddSubmonoid.subset_closure ha
    have hsplit : ¬ ∀ y ∈ S, ∀ z ∈ S, x = y + z → y = 0 ∨ z = 0 :=
      fun H => ha ⟨hx, h0, H⟩
    push Not at hsplit
    obtain ⟨y, hy, z, hz, he, hY, hZ⟩ := hsplit
    have hsum : degree y + degree z = n := by simpa [he,degree_add] using hn
    have hypos := mt (degree_zero_iff y).mp hY
    have hzpos := mt (degree_zero_iff z).mp hZ
    rw [he]
    exact (AddSubmonoid.closure A).add_mem (ih (degree y) (by omega) hy rfl) (ih (degree z) (by omega) hz rfl)

theorem atoms_minimal {a b d : ℕ} (G : Set (Point d))
    (hG : (AddSubmonoid.closure G : Set (Point d)) = graded a b d) :
    atoms (graded a b d) ⊆ G := by
  rintro x ⟨hx, h0, ha⟩
  have hx' : x ∈ AddSubmonoid.closure G := by
    change x ∈ (AddSubmonoid.closure G : Set (Point d))
    rwa [hG]
  suffices ∀ y (h : y ∈ AddSubmonoid.closure G), y = x → x ∈ G from this x hx' rfl
  intro y hy
  induction hy using AddSubmonoid.closure_induction with
  | mem t ht => exact fun he => he ▸ ht
  | zero => exact fun he => (h0 he.symm).elim
  | add t u ht hu it iu =>
    intro he
    have ht' : t ∈ graded a b d := hG ▸ ht
    have hu' : u ∈ graded a b d := hG ▸ hu
    rcases ha t ht' u hu' he.symm with h | h
    · exact iu (by simpa [h] using he)
    · exact it (by simpa [h] using he)

end TaskP.GradedWilf
