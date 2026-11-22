import Mathlib

/-! Beaton–Cameron, journal Question 6 (arXiv Question 5.3). -/

namespace TaskN.Antichain.Challenge

open Polynomial

/-- The generating polynomial of independent vertex subsets, including the empty set. -/
noncomputable def independencePolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ s : Finset V, if G.IsIndepSet (s : Set V) then X ^ s.card else 0

/-- The source explicitly identifies its endpoint with the largest real independence root. -/
def LargestRoot {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℝ) : Prop :=
  IsGreatest {x : ℝ | (independencePolynomial G).eval x = 0} r

/-- H precedes G when its polynomial is larger throughout the interval ending at zero.
    The lower endpoint belongs to G. The family below supplies a largest root for every tree. -/
def Precedes {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∀ r : ℝ, LargestRoot G r → ∀ x ∈ Set.Icc r 0,
    (independencePolynomial G).eval x ≤ (independencePolynomial H).eval x

/-- Trees on the same n vertices with mutually incomparable independent-set polynomials. -/
def HasAntichain (n k : ℕ) : Prop :=
  ∃ F : Fin k → SimpleGraph (Fin n),
    (∀ i, (F i).IsTree ∧ ∃ r, LargestRoot (F i) r) ∧
    ∀ i j, i ≠ j → ¬ Precedes (F i) (F j) ∧ ¬ Precedes (F j) (F i)

/-- Quantitative strengthening at every order n ≥ 11. -/
def WidthLowerBound : Prop :=
  ∀ n : ℕ, 11 ≤ n → HasAntichain n (n / 11 + 1)

/-- Question 6: each prescribed finite antichain size occurs at some common order. -/
def ArbitrarilyLarge : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, HasAntichain n k

end TaskN.Antichain.Challenge
