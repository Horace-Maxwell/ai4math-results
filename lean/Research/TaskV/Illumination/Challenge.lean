import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.RealVectorSpace

namespace PrismIllumination

abbrev Space := Fin 3 → ℝ

def cube : Set Space := {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1}

def prism : Set Space := {p | p ∈ cube ∧ p 0 + p 1 ≤ 1}

def edge : Set Space := {p | p ∈ cube ∧ p 0 = 1 ∧ p 1 = 1}

def Illuminates (K : Set Space) (u p : Space) : Prop :=
  ∃ t : ℝ, 0 < t ∧ p + t • u ∈ interior K

def CanLight (K : Set Space) (n : ℕ) : Prop :=
  ∃ u : Fin n → Space, (∀ i, u i ≠ 0) ∧
    ∀ p ∈ frontier K, ∃ i, Illuminates K (u i) p

def Exact (K : Set Space) (n : ℕ) : Prop :=
  CanLight K n ∧ ∀ m, CanLight K m → n ≤ m

def Trichotomy : Prop :=
  ∀ K : Set Space, IsCompact K → Convex ℝ K → prism ⊆ K → K ⊆ cube →
    (Disjoint K edge → Exact K 6) ∧
    (¬ Disjoint K edge → K ≠ cube → Exact K 7) ∧
    (K = cube → Exact K 8)

end PrismIllumination
