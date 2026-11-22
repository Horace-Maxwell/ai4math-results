import Mathlib

namespace TaskR.CSS.Challenge

open Set MeasureTheory
open scoped BigOperators ENNReal

abbrev Space := Fin 4 → ℝ
abbrev Lattice := Fin 4 → ℤ

def embed (z : Lattice) : Space := fun i => (z i : ℝ)

def weight : Lattice := ![2, 1, 1, 1]

def e (i : Fin 4) : Lattice := Pi.single i 1

def vertices : Set Space := insert (embed (-weight)) (range fun i => embed (e i))

noncomputable def P : Set Space := convexHull ℝ vertices

/-- The reference simplex has vertices zero and the four standard lattice basis vectors. -/
noncomputable def unitSimplex : Set Space :=
  convexHull ℝ (insert 0 (range fun i => embed (e i)))

/-- Euclidean volume normalized to make a unimodular lattice simplex have volume one. -/
noncomputable def normalizedVolume (K : Set Space) : ℝ≥0∞ := volume K / volume unitSimplex

/-- Every real point belongs to a lattice translate of a scaled body. -/
def Covers (K : Set Space) (r : ℝ) : Prop :=
  ∀ x : Space, ∃ z : Lattice, ∃ y ∈ K, x = embed z + r • y

/-- A larger family than CSS's generated family. Its leaves include every positive-dimensional
standard terminal simplex in any lattice coordinates, since its vertices sum to zero.
Its hull constructor allows even noncomplementary factors and does not constrain the origin. -/
inductive Generated : Set Space → Prop
  | leaf (s : Finset Lattice) (hcard : 2 ≤ s.card) (hsum : ∑ z ∈ s, z = 0) :
      Generated (convexHull ℝ (embed '' (↑s : Set Lattice)))
  | translate {K : Set Space} (h : Generated K) (z : Lattice) :
      Generated ((fun x => embed z + x) '' K)
  | join {K L : Set Space} (hK : Generated K) (hL : Generated L) :
      Generated (convexHull ℝ (K ∪ L))

def NonHollow : Prop := (0 : Space) ∈ interior P

def Radius : Prop := IsLeast {r : ℝ | 0 ≤ r ∧ Covers P r} 2

def Volume : Prop := normalizedVolume P = 6

def OutsideList : Prop := ¬ Generated P

end TaskR.CSS.Challenge
