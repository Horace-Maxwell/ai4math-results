import Mathlib

namespace TaskT.HellyFive

abbrev Space (n : ℕ) := Fin n → ℝ
abbrev Grid (n : ℕ) := Fin n → ℤ

def embed {n : ℕ} (x : Grid n) : Space n := fun i => x i

/-- Lattice points common to the indexed subfamily, including the empty subfamily. -/
def commonGrid {n m : ℕ} (C : Fin m → Set (Space n)) (s : Finset (Fin m)) : Set (Grid n) :=
  {z | ∀ i ∈ s, embed z ∈ C i}

/-- The admissible bounds in Definition 1, specialized to exactly five lattice points. -/
def PreservesFive (n t : ℕ) : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ C : Fin m → Set (Space n),
    (∀ i, Convex ℝ (C i)) → (commonGrid C Finset.univ).encard = 5 →
    ∃ s : Finset (Fin m), s.card ≤ t ∧ (commonGrid C s).encard = 5

/-- Count the geometric extreme points of a lattice polytope, permitting every affine dimension. -/
def attainableCounts (n : ℕ) : Set ℕ :=
  {t | ∃ V : Finset (Grid n),
    let P := convexHull ℝ (embed '' (V : Set (Grid n)))
    (P.extremePoints ℝ).encard = (t : ℕ∞) ∧
      ({z : Grid n | embed z ∈ P ∧ embed z ∉ P.extremePoints ℝ} : Set (Grid n)).encard = 5}

def value (n : ℕ) : ℕ :=
  if n = 1 then 2 else if n = 2 then 7 else if n = 3 then 18 else 2 ^ (n + 1) + 5

def ExactHellyFive : Prop :=
  ∀ n : ℕ, 0 < n → IsLeast {t : ℕ | PreservesFive n t} (value n)

def ExactVertexFive : Prop :=
  ∀ n : ℕ, 0 < n → IsGreatest (attainableCounts n) (value n)

end TaskT.HellyFive
