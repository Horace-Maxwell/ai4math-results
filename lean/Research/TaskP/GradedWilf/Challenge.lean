import Mathlib

namespace TaskP.GradedWilf.Challenge

abbrev Point (d : ℕ) := Fin d → ℕ

def degree {d : ℕ} (x : Point d) : ℕ := ∑ i, x i

def scalar (a b : ℕ) : AddSubmonoid ℕ := AddSubmonoid.closure {a, b}

def graded (a b d : ℕ) : Set (Point d) := {x | degree x ∈ scalar a b}

def belowGaps {d : ℕ} (S : Set (Point d)) : Set (Point d) :=
  {x | ∃ h, h ∉ S ∧ x ≤ h}

def atoms {d : ℕ} (S : Set (Point d)) : Set (Point d) :=
  {x | x ∈ S ∧ x ≠ 0 ∧ ∀ y ∈ S, ∀ z ∈ S, x = y + z → y = 0 ∨ z = 0}

/-- The actual finite minimal generators and the coordinatewise gap counts. -/
def Wilf : Prop :=
  ∀ a b d : ℕ, 2 ≤ a → a < b → a.Coprime b → 0 < d →
    let S := graded a b d
    let C := belowGaps S
    let A := atoms S
    C.Finite ∧ A.Finite ∧
    (AddSubmonoid.closure A : Set (Point d)) = S ∧
    (∀ G : Set (Point d), (AddSubmonoid.closure G : Set (Point d)) = S → A ⊆ G) ∧
    d * C.ncard ≤ A.ncard * (C ∩ S).ncard

end TaskP.GradedWilf.Challenge
