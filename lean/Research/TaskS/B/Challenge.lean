import Mathlib

open scoped BigOperators
namespace TaskS.B.Challenge

abbrev Space (n : ℕ) := Fin n → ℝ
abbrev Lattice (n : ℕ) := Fin n → ℤ

def embed {n : ℕ} (z : Lattice n) : Space n := fun j => z j

noncomputable def vertex (n : ℕ) : Fin (n + 1) → Space n :=
  Fin.cases (fun _ => -1) (fun j => Pi.single j 1)

noncomputable def terminal (n : ℕ) : Set (Space n) :=
  convexHull ℝ (Set.range (vertex n))

/-- The image of the standard lattice is a full lattice in the target. -/
def LatticeProjection {n i : ℕ} (p : Space n →ₗ[ℝ] Space i) : Prop :=
  Function.Surjective p ∧ ∃ b : Module.Basis (Fin i) ℝ (Space i),
    Set.range (fun z : Lattice n => p (embed z)) =
      Set.range (fun w : Lattice i => ∑ j, (w j : ℝ) • b j)

/-- Covering the entire target by projected lattice translates of the dilation. -/
def Covers {n i : ℕ} (p : Space n →ₗ[ℝ] Space i) (r : ℝ) : Prop :=
  ∀ x : Space i, ∃ z : Lattice n, ∃ y ∈ terminal n, x = p (embed z) + r • p y

/-- The first clause bounds every admissible projection. The second attains the bound
as the least nonnegative covering scale of a projection. -/
def ConjectureB : Prop :=
  ∀ (n i : ℕ), 0 < i → i ≤ n →
    (∀ p : Space n →ₗ[ℝ] Space i, LatticeProjection p → Covers p ((i : ℝ) / 2)) ∧
    ∃ p : Space n →ₗ[ℝ] Space i, LatticeProjection p ∧
      IsLeast {r : ℝ | 0 ≤ r ∧ Covers p r} ((i : ℝ) / 2)

end TaskS.B.Challenge
