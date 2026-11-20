import Mathlib

namespace TaskL.Semigroup.Challenge

/-- Nonnegative integers under addition; a numerical semigroup has finite complement. -/
def Numerical (S : AddSubmonoid ℕ) : Prop :=
  ((↑S : Set ℕ)ᶜ).Finite

/-- Binary irreducibility among numerical oversemigroups. -/
def Irreducible (Q : AddSubmonoid ℕ) : Prop :=
  Numerical Q ∧ ∀ A B : AddSubmonoid ℕ, Numerical A → Numerical B →
    Q = A ⊓ B → Q = A ∨ Q = B

/-- Membership in the intersection of a finite family; the empty intersection is ℕ. -/
def Represents (S : AddSubmonoid ℕ) (D : Finset (AddSubmonoid ℕ)) : Prop :=
  ∀ n : ℕ, n ∈ S ↔ ∀ Q ∈ D, n ∈ Q

def Decomposition (S : AddSubmonoid ℕ) (D : Finset (AddSubmonoid ℕ)) : Prop :=
  (∀ Q ∈ D, Irreducible Q) ∧ Represents S D ∧
    ∀ E : Finset (AddSubmonoid ℕ), E ⊂ D → ¬ Represents S E

def HasLength (S : AddSubmonoid ℕ) (j : ℕ) : Prop :=
  ∃ D : Finset (AddSubmonoid ℕ), Decomposition S D ∧ D.card = j

/-- The least positive element, expressed without an arbitrary value at an empty set. -/
def HasMultiplicity (S : AddSubmonoid ℕ) (m : ℕ) : Prop :=
  0 < m ∧ m ∈ S ∧ ∀ s ∈ S, 0 < s → m ≤ s

/-- Existence ensures that the decomposition-length interval is nonempty. -/
def LengthsExist : Prop :=
  ∀ S : AddSubmonoid ℕ, Numerical S → ∃ j, HasLength S j

/-- Conjecture 1.1 with the ordinary empty-intersection convention. -/
def LengthsInterval : Prop :=
  ∀ S : AddSubmonoid ℕ, Numerical S → ∀ a b j : ℕ,
    HasLength S a → HasLength S b → a ≤ j → j ≤ b → HasLength S j

/-- The positive-length convention used in the 2024 source. -/
def PositiveLengthsInterval : Prop :=
  ∀ S : AddSubmonoid ℕ, Numerical S → ∀ a b j : ℕ,
    (0 < a ∧ HasLength S a) → (0 < b ∧ HasLength S b) →
    a ≤ j → j ≤ b → 0 < j ∧ HasLength S j

/-- Conjecture 3.9, with m = 2k, for every qualifying realized length j. -/
def EvenMultiplicityDescent : Prop :=
  ∀ S : AddSubmonoid ℕ, Numerical S → ∀ k j : ℕ, HasMultiplicity S (2*k) →
    k < j → j < 2*k → HasLength S j → HasLength S (j-1)

end TaskL.Semigroup.Challenge
