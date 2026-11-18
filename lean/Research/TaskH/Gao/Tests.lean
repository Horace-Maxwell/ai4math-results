import Research.TaskH.Gao.Challenge

set_option autoImplicit false
universe u
namespace TaskH.Gao.Tests
variable {V : Type u}

theorem family_expansion (G : SimpleGraph V) (x y : V) (k a d : ℕ)
    (p : Fin k → G.Walk x y) :
    AdmissiblePathFamily G x y k a d p ↔
      (2 ≤ a ∧ (d = 1 ∨ d = 2) ∧ ∀ i : Fin k,
        (p i).IsPath ∧ (p i).length = a + i.val * d) := Iff.rfl

theorem has_paths_expansion (G : SimpleGraph V) (x y : V) (k : ℕ) :
    HasAdmissiblePaths G x y k ↔
      (∃ a d : ℕ, ∃ p : Fin k → G.Walk x y, AdmissiblePathFamily G x y k a d p) := Iff.rfl

theorem claim_expansion : RootedPathClaim.{u} ↔
    (∀ k : ℕ, 1 ≤ k → ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (x y : V),
      TaskH.Fan.RootedTwoConnected G x y →
        TaskH.Fan.NonrootDegreeAtLeast G x y (k + 1) → HasAdmissiblePaths G x y k) := Iff.rfl

theorem zero_start_rejected (G : SimpleGraph V) (x y : V) (k d : ℕ)
    (p : Fin k → G.Walk x y) : ¬AdmissiblePathFamily G x y k 0 d p := by
  intro h
  have ha := h.1
  omega

theorem step_three_rejected (G : SimpleGraph V) (x y : V) (k a : ℕ)
    (p : Fin k → G.Walk x y) : ¬AdmissiblePathFamily G x y k a 3 p := by
  intro h
  rcases h.2.1 with h | h <;> omega

theorem every_length_ge_two (G : SimpleGraph V) (x y : V) (k a d : ℕ)
    (p : Fin k → G.Walk x y) (h : AdmissiblePathFamily G x y k a d p) :
    ∀ i : Fin k, 2 ≤ (p i).length := by
  intro i
  have ha := h.1
  have hl := (h.2.2 i).2
  omega

#print axioms family_expansion
#print axioms has_paths_expansion
#print axioms claim_expansion
#print axioms zero_start_rejected
#print axioms step_three_rejected
#print axioms every_length_ge_two
end TaskH.Gao.Tests
