import Mathlib

/-! Alikhani–Brown–Jahari, Question 3.2 (Filomat 30, 2016, p. 176). -/

open Filter Polynomial
open scoped Topology

namespace TaskP.GraphRootRadius.Challenge

/-- Each vertex lies in the chosen set or is adjacent to one of its members. -/
def Dominates {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v, v ∈ S ∨ ∃ u ∈ S, G.Adj v u

noncomputable def dominationPolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℂ[X] := by
  classical
  exact ∑ S : Finset V, if Dominates G S then X ^ S.card else 0

/-- The central clique is the left summand. A petal has a copy index and a vertex of B. -/
def petalJoin {V : Type*} (a m : ℕ) (B : SimpleGraph V) :
    SimpleGraph (Fin a ⊕ (Fin m × V)) where
  Adj
    | .inl i, .inl j => i ≠ j
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr x, .inr y => x.1 = y.1 ∧ B.Adj x.2 y.2
  symm := by
    constructor
    rintro (i | x) (j | y) h
    · exact Ne.symm h
    · trivial
    · trivial
    · exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    rintro (i | x)
    · exact fun h => h rfl
    · exact fun h => B.loopless.irrefl _ h.2

noncomputable def closedNeighborhood {V : Type*} [Fintype V]
    (B : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact insert v (B.neighborFinset v)

noncomputable def minimumSize {V : Type*} [Fintype V] (B : SimpleGraph V) : ℕ := by
  classical
  exact B.minDegree + 1

/-- A repeated closed neighborhood is counted once in the image. -/
noncomputable def minimumCount {V : Type*} [Fintype V] (B : SimpleGraph V) : ℕ := by
  classical
  exact ((Finset.univ.image (closedNeighborhood B)).filter
    (fun S => S.card = minimumSize B)).card

/-- Supremum of the norms of all complex roots. The theorem also asserts attainment. -/
noncomputable def rootRadius {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sSup {r : ℝ | ∃ z : ℂ, (dominationPolynomial G).eval z = 0 ∧ ‖z‖ = r}

noncomputable def scale (a c s m : ℕ) : ℝ :=
  ((c : ℝ) * s * m / (a * Real.log m)) ^ (1 / (c : ℝ))

/-- An actual root of maximum modulus exists for each of the nonempty joins. -/
def Attainment : Prop :=
  ∀ {V : Type} [Fintype V] [Nonempty V] (B : SimpleGraph V)
    (a m : ℕ), 0 < a → 0 < m →
      IsGreatest {r : ℝ | ∃ z : ℂ,
        (dominationPolynomial (petalJoin a m B)).eval z = 0 ∧ ‖z‖ = r}
        (rootRadius (petalJoin a m B))

/-- The petal and the positive central clique size are fixed throughout each limit. -/
def GeneralAsymptotic : Prop :=
  ∀ {V : Type} [Fintype V] [Nonempty V] (B : SimpleGraph V)
    (a : ℕ), 0 < a →
      Tendsto (fun m : ℕ =>
        rootRadius (petalJoin a m B) / scale a (minimumSize B) (minimumCount B) m)
        atTop (𝓝 1)

/-- A friendship graph has a single common center and m disjoint edges. -/
abbrev friendshipGraph (m : ℕ) := petalJoin 1 m (⊤ : SimpleGraph (Fin 2))

def FriendshipAsymptotic : Prop :=
  Tendsto (fun m : ℕ => rootRadius (friendshipGraph m) /
    Real.sqrt (2 * (m : ℝ) / Real.log m)) atTop (𝓝 1)

end TaskP.GraphRootRadius.Challenge
