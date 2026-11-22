import Mathlib

/-! Soprunov–Soprunova, Problems 2 and 3. Finite convex hulls and all Minkowski
summands are taken in the real ambient space, with the usual integer lattice. -/

namespace TaskP.GeomSimplex.Challenge

abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Space (d : ℕ) := Fin d → ℝ

def realPoint {d : ℕ} (a : Lattice d) : Space d := fun i => a i

def polytope {d : ℕ} (vertices : Finset (Lattice d)) : Set (Space d) :=
  convexHull ℝ (realPoint '' (vertices : Set (Lattice d)))

def simplex {d : ℕ} (vertices : Fin (d + 1) → Lattice d) : Set (Space d) :=
  convexHull ℝ (Set.range (realPoint ∘ vertices))

def fullSimplex {d : ℕ} (vertices : Fin (d + 1) → Lattice d) : Prop :=
  AffineIndependent ℝ (realPoint ∘ vertices)

def dilate {d : ℕ} (t : ℕ) (P : Set (Space d)) : Set (Space d) :=
  (fun x => (t : ℝ) • x) '' P

/-- The Minkowski sum of k positive-dimensional lattice polytopes is contained in P.
Its elements are precisely the sums obtained by choosing one real point in each factor. -/
def packs {d : ℕ} (P : Set (Space d)) (k : ℕ) : Prop :=
  ∃ V : Fin k → Finset (Lattice d),
    (∀ i, 1 < (V i).card) ∧
    ∀ x : Fin k → Space d, (∀ i, x i ∈ polytope (V i)) → ∑ i, x i ∈ P

/-- An attained maximum, with its upper bound stated for every possible packing. -/
def lengthIs {d : ℕ} (P : Set (Space d)) (n : ℕ) : Prop :=
  packs P n ∧ ∀ k, packs P k → k ≤ n

/-- The lattice diameter is one precisely when two distinct lattice points occur
and no three distinct lattice points lie on a real affine line. -/
def diameterOne {d : ℕ} (P : Set (Space d)) : Prop :=
  (∃ a b : Lattice d, a ≠ b ∧ realPoint a ∈ P ∧ realPoint b ∈ P) ∧
  ∀ a b c : Lattice d, realPoint a ∈ P → realPoint b ∈ P → realPoint c ∈ P →
    Collinear ℝ ({realPoint a, realPoint b, realPoint c} : Set (Space d)) →
    a = b ∨ a = c ∨ b = c

/-- All positive t in a residue class use its same rational linear constituent.
The value is the attained maximum of Definition 1.1. -/
def quasiLinearLengths {d : ℕ} (P : Set (Space d)) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ slope intercept : ℕ → ℚ,
    ∀ t : ℕ, 0 < t → ∃ n : ℕ, lengthIs (dilate t P) n ∧
      (n : ℚ) = slope (t % k) * t + intercept (t % k)

def verticesT : Fin 4 → Lattice 3 :=
  ![![1, 0, 1], ![3, 3, 1], ![2, 0, 3], ![0, 3, 3]]

def verticesU : Fin 4 → Lattice 3 :=
  ![![0, 0, 0], ![1, 0, 0], ![0, 0, 1], ![13, 18, 1]]

def problemThreeWitness {d : ℕ} (v : Fin (d + 1) → Lattice d) : Prop :=
  fullSimplex v ∧ lengthIs (simplex v) 2 ∧ diameterOne (simplex v)

def problemTwoWitness {d : ℕ} (v : Fin (d + 1) → Lattice d) : Prop :=
  fullSimplex v ∧ lengthIs (simplex v) 1 ∧
    (∀ t : ℕ, 2 ≤ t → lengthIs (dilate t (simplex v)) (3 * t)) ∧
    ¬ quasiLinearLengths (simplex v)

def TetrahedronDiameter : Prop := problemThreeWitness verticesT

def TetrahedronDilations : Prop := problemTwoWitness verticesU

def EveryDimensionDiameter : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ v : Fin (d + 1) → Lattice d, problemThreeWitness v

def EveryDimensionDilations : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ v : Fin (d + 1) → Lattice d, problemTwoWitness v

end TaskP.GeomSimplex.Challenge
