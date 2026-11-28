import Research.TaskV.Stanley.ChallengeA

/-! Tagged terminal reconstruction from the ordinary chromatic symmetric function.
The marked vertices are leaves of the induced nonleaf core of the ordinary tree. -/

namespace StanleyContinuation

noncomputable section
open scoped BigOperators

/-- A core leaf whose leaf-component order occurs elsewhere in the core. -/
def untaggedCoreLeaf {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  v ∈ core G ∧ ((neighbors G v) ∩ core G).card = 1 ∧
    ∃ u ∈ core G, u ≠ v ∧ coreWeight G u = coreWeight G v

/-- Proper trees whose core weights are atomic among subset sums and whose core
has at most one leaf without a globally unique weight. -/
def PeelingWeights {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  2 ≤ (core G).card ∧
  (∀ v ∈ core G, 2 ≤ coreWeight G v) ∧
  (∀ v ∈ core G, ∀ P : Finset (Fin n), P ⊆ core G → 2 ≤ P.card →
    (∑ u ∈ P, coreWeight G u) ≠ coreWeight G v) ∧
  ∀ v u, untaggedCoreLeaf G v → untaggedCoreLeaf G u → v = u

def PeelingReconstruction : Prop :=
  ∀ (n m : ℕ) (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)),
    G.IsTree → H.IsTree → PeelingWeights G → SameCSF G H → Nonempty (G ≃g H)

end
end StanleyContinuation
