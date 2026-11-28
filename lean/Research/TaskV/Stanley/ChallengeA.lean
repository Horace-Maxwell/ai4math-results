import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Card

/-! Ordinary chromatic symmetric functions, via the coefficients of all finite-colour
specializations.  A coloring is counted once for its ordered vector of color-class sizes. -/
namespace StanleyContinuation

noncomputable section
open scoped BigOperators
open Finset

def colorCoefficient {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (multiplicity : Fin k → ℕ) : ℕ :=
  Nat.card { f : Fin n → Fin k //
    (∀ i j, G.Adj i j → f i ≠ f j) ∧
    ∀ c, Nat.card {i : Fin n // f i = c} = multiplicity c }

def SameCSF {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) : Prop :=
  ∀ k (multiplicity : Fin k → ℕ),
    colorCoefficient G k multiplicity = colorCoefficient H k multiplicity

def neighbors {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) := by
  classical exact univ.filter (G.Adj v)

def core {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n) := by
  classical exact univ.filter fun v => (neighbors G v).card ≠ 1

def coreWeight {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  1 + ((neighbors G v) \ core G).card

def DecodableLeafAnchors {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  2 ≤ (core G).card ∧
  (∀ v ∈ core G, 2 ≤ coreWeight G v) ∧
  ∃ A : Finset (Fin n),
    A ⊆ core G ∧
    (∀ a ∈ A, ∀ v ∈ core G, coreWeight G v = coreWeight G a → v = a) ∧
    (∀ v ∈ core G, ((neighbors G v) ∩ core G).card = 1 → v ∈ A) ∧
    ∀ P Q : Finset (Fin n), P ⊆ core G → Q ⊆ core G →
      (∑ v ∈ P, coreWeight G v) = (∑ v ∈ Q, coreWeight G v) →
      ∀ a ∈ A, (a ∈ P ↔ a ∈ Q)

def AnchorReconstruction : Prop :=
  ∀ (n m : ℕ) (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)),
    G.IsTree → H.IsTree → DecodableLeafAnchors G → SameCSF G H → Nonempty (G ≃g H)

end
end StanleyContinuation
