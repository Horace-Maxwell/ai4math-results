import Mathlib

/-!
Task H internal rooted two-path base. Statement only, no asserted theorem.
All output paths live in G itself. Only the connectivity test adds the root edge.
The original TaskH Challenge and every accepted partial target remain unchanged.
-/
set_option autoImplicit false

universe u

namespace TaskH.Fan

variable {V : Type u}

/-- Ordinary vertex 2-connectivity, including the order-at-least-three convention. -/
def TwoConnected [Fintype V] (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ G.Connected ∧
    ∀ z : V, (G.induce {v | v ≠ z}).Connected

/-- The extra root edge is only a test of connectivity, not an output-path edge. -/
def RootedTwoConnected [Fintype V] (G : SimpleGraph V) (x y : V) : Prop :=
  x ≠ y ∧ TwoConnected (G ⊔ SimpleGraph.edge x y)

/-- The actual G-neighbor count at every vertex other than the two roots. -/
noncomputable def NonrootDegreeAtLeast (G : SimpleGraph V) (x y : V) (d : ℕ) : Prop :=
  ∀ v : V, v ≠ x → v ≠ y → d ≤ (G.neighborSet v).ncard

/-- The shorter path is listed first; witnesses have no repeated vertices. -/
def TwoPathWitness {G : SimpleGraph V} {x y : V}
    (p q : G.Walk x y) : Prop :=
  p.IsPath ∧ q.IsPath ∧ 2 ≤ p.length ∧ 2 ≤ q.length ∧
    (p.length + 1 = q.length ∨ p.length + 2 = q.length)

/-- Both paths use actual edges of the original G, not the augmented graph. -/
def HasTwoPaths (G : SimpleGraph V) (x y : V) : Prop :=
  ∃ p q : G.Walk x y, TwoPathWitness p q

/-- Known rooted base theorem to be proved, over all finite vertex types. -/
noncomputable def TwoPathClaim : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (x y : V),
    RootedTwoConnected G x y → NonrootDegreeAtLeast G x y 3 → HasTwoPaths G x y

#print axioms TwoConnected
#print axioms RootedTwoConnected
#print axioms NonrootDegreeAtLeast
#print axioms TwoPathWitness
#print axioms HasTwoPaths
#print axioms TwoPathClaim

end TaskH.Fan
