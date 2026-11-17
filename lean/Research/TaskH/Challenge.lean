import Mathlib

/-!
Task H: Choi--Sieniawski, arXiv:2611.13580v1, Question 2.
Statement-only candidate. The all-k question and the k=4 partial target are
separate propositions. None of these propositions is assumed as an axiom.

Cycles are the edge sets of genuine Mathlib Walk.IsCycle witnesses. Thus
changing the starting point or direction does not create another cycle.
Criticality quantifies over all proper Subgraph objects, including edge
deletions, and uses the graph on the subgraph's actual vertex set.
-/
set_option autoImplicit false

universe u

namespace TaskH.Challenge

variable {V : Type u}

/-- A cycle has an actual closed-walk witness, with no repeated cycle edge. -/
noncomputable def IsCycleEdgeSet (G : SimpleGraph V) (s : Finset (Sym2 V)) : Prop := by
  classical
  exact ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.edges.toFinset = s

/-- The division condition refers to the number of distinct cycle edges.
The equality with the witness's walk length is a required bridge lemma. -/
def ModCycleEdgeSets (k : ℕ) (G : SimpleGraph V) : Set (Finset (Sym2 V)) :=
  {s | IsCycleEdgeSet G s ∧ k ∣ s.card}

/-- Finite for every finite vertex type; no walk representatives are counted. -/
noncomputable def modCycleCount (k : ℕ) (G : SimpleGraph V) : ℕ :=
  (ModCycleEdgeSets k G).ncard

/-- (k+1)-critical in the original, proper-subgraph sense. -/
def IsCriticalPlus (k : ℕ) (G : SimpleGraph V) : Prop :=
  G.chromaticNumber = (k + 1 : ℕ) ∧
    ∀ S : G.Subgraph, S ≠ ⊤ → S.coe.Colorable k

def IsCompleteOfOrder (G : SimpleGraph V) (n : ℕ) : Prop :=
  Nonempty (G ≃g (⊤ : SimpleGraph (Fin n)))

/-- The original lower bound, with the original parentheses. -/
def bound (k : ℕ) : ℕ := (k + 1).factorial / (2 * k)

/-- One value of k, over all finite vertex types. -/
def EqualityCase (k : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
    IsCriticalPlus k G → modCycleCount k G = bound k →
      IsCompleteOfOrder G (k + 1)

/-- Full Question 2. A proof for k=4 alone does not prove this proposition. -/
def Question2 : Prop := ∀ k : ℕ, 4 ≤ k → EqualityCase.{u} k

/-- A negative full answer must supply the critical graph and exact count. -/
def CounterexampleToQuestion2 : Prop :=
  ∃ (k : ℕ), 4 ≤ k ∧ ∃ (V : Type u) (_ : Fintype V) (G : SimpleGraph V),
    IsCriticalPlus k G ∧ modCycleCount k G = bound k ∧
      ¬ IsCompleteOfOrder G (k + 1)

/-- The partial target supported by the first complete mathematical manuscript. -/
def CaseFour : Prop := EqualityCase.{u} 4

/-- The concrete positive example must also pass a separate regression theorem. -/
def CompleteFiveCheck : Prop :=
  IsCriticalPlus 4 (⊤ : SimpleGraph (Fin 5)) ∧
    modCycleCount 4 (⊤ : SimpleGraph (Fin 5)) = 15 ∧ bound 4 = 15

end TaskH.Challenge
