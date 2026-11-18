import Research.TaskH.Fan.Challenge

set_option autoImplicit false

universe u

namespace TaskH.Fan.Tests

open SimpleGraph

variable {V : Type u}

-- Exact definition-expansion regressions only: none asserts the two-path theorem.
example [Fintype V] (G : SimpleGraph V) :
    TwoConnected G ↔ (3 ≤ Fintype.card V ∧ G.Connected ∧
      ∀ z : V, (G.induce {v | v ≠ z}).Connected) := Iff.rfl

example [Fintype V] (G : SimpleGraph V) (x y : V) :
    RootedTwoConnected G x y ↔
      (x ≠ y ∧ TwoConnected (G ⊔ SimpleGraph.edge x y)) := Iff.rfl

example (G : SimpleGraph V) (x y : V) (d : ℕ) :
    NonrootDegreeAtLeast G x y d ↔
      (∀ v : V, v ≠ x → v ≠ y → d ≤ (G.neighborSet v).ncard) := Iff.rfl

example {G : SimpleGraph V} {x y : V} (p q : G.Walk x y) :
    TwoPathWitness p q ↔ (p.IsPath ∧ q.IsPath ∧ 2 ≤ p.length ∧ 2 ≤ q.length ∧
      (p.length + 1 = q.length ∨ p.length + 2 = q.length)) := Iff.rfl

example (G : SimpleGraph V) (x y : V) :
    HasTwoPaths G x y ↔ (∃ p q : G.Walk x y, TwoPathWitness p q) := Iff.rfl

example : TwoPathClaim.{u} ↔
    (∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (x y : V),
      RootedTwoConnected G x y → NonrootDegreeAtLeast G x y 3 → HasTwoPaths G x y) :=
  Iff.rfl

end TaskH.Fan.Tests
