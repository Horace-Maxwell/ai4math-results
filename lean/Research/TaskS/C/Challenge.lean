import Mathlib

namespace TaskS.C.Challenge

open Set
open scoped BigOperators

abbrev Space (d : ℕ) := Fin d → ℝ
abbrev Lattice (d : ℕ) := Fin d → ℤ

def embed {d : ℕ} (u : Lattice d) : Space d := fun k => (u k : ℝ)

/-- An integer vector whose coordinates generate the unit ideal. -/
def Primitive {d : ℕ} (u : Lattice d) : Prop :=
  ∃ a : Lattice d, ∑ k, a k * u k = 1

def vertices {d : ℕ} (u : Fin (d+1) → Lattice d) (ω : Fin (d+1) → ℝ)
    (j : Fin (d+1)) : Space d := ω j • embed (u j)

noncomputable def simplex {d : ℕ} (v : Fin (d+1) → Space d) : Set (Space d) :=
  convexHull ℝ (range v)

/-- Normalized simplex volume in standard lattice coordinates via homogeneous determinants. -/
noncomputable def volume {d : ℕ} (v : Fin (d+1) → Space d) : ℝ :=
  |(Matrix.of (fun i => Fin.cons (1 : ℝ) (v i))).det|

/-- Normalized volume of the facet opposite i after projecting along the primitive ray u_i.
The determinant takes the primitive kernel generator followed by lifts of the projected
edge vectors, in the ambient lattice coordinates. -/
noncomputable def projectedVolume {n : ℕ} (v : Fin (n+2) → Space (n+1))
    (u : Fin (n+2) → Lattice (n+1)) (i : Fin (n+2)) : ℝ :=
  |(Matrix.of (Fin.cons (embed (u i)) (fun k : Fin n =>
    v (i.succAbove k.succ) - v (i.succAbove 0)))).det|

def Covers {d : ℕ} (K : Set (Space d)) (r : ℝ) : Prop :=
  ∀ x : Space d, ∃ z : Lattice d, ∃ y ∈ K, x = embed z + r • y

/-- CSS Definition 1.5 and Conjecture C, with d=n+1 including dimension one.
The covering conclusion at the asserted scale includes the covering-radius bound. -/
def conjectureC : Prop :=
  ∀ (n : ℕ) (u : Fin (n+2) → Lattice (n+1)) (ω : Fin (n+2) → ℝ),
    (∀ i, Primitive (u i)) → (∀ i, 0 < ω i) →
    let v := vertices u ω
    0 < volume v → (0 : Space (n+1)) ∈ interior (simplex v) →
    Covers (simplex v) ((∑ i, projectedVolume v u i) / (2 * volume v))

end TaskS.C.Challenge
