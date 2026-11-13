import Research.AxialMSZ.Challenge

/-!
Task G, Shpectorov's question in Gorshkov--Shpectorov arXiv:2606.30048v1,
source main.tex lines 529--544. Statement-only candidate, not a theorem.
The field choices are explicit search domains, each sufficient for the existential question.
Direct indecomposability excludes every nontrivial direct sum of ideals, not merely B+B.
One-dimensionality of the space of all associating bilinear forms is a stronger optional target.
No nondegeneracy or unit is imposed by the original question.
-/
set_option autoImplicit false

namespace TaskG.Challenge
open AxialMSZ.Challenge

/- Closed field-instance side conditions; no research claim is assumed. -/
instance prime_five : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
instance prime_seven : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
instance prime_eleven : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩

section General
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def IsAlgebraAutomorphism (μ : V →ₗ[K] V →ₗ[K] V) (g : V ≃ₗ[K] V) : Prop :=
  ∀ u v, g (μ u v) = μ (g u) (g v)

def DirectlyIndecomposable (μ : V →ₗ[K] V →ₗ[K] V) : Prop :=
  ∀ I J : Submodule K V, IsIdeal μ I → IsIdeal μ J →
    Disjoint I J → I ⊔ J = ⊤ → I = ⊥ ∨ J = ⊥

def FormSpaceOneDimensional (μ : V →ₗ[K] V →ₗ[K] V)
    (β : V →ₗ[K] V →ₗ[K] K) : Prop :=
  β ≠ 0 ∧ ∀ γ : V →ₗ[K] V →ₗ[K] K, IsFrobeniusForm μ γ → ∃ c : K, γ = c • β

def HasNoIdentity (μ : V →ₗ[K] V →ₗ[K] V) : Prop :=
  ¬ ∃ e : V, ∀ v, μ e v = v ∧ μ v e = v

/-- Every datum is an actual multiplication, form, generator set or invertible linear map. -/
def WitnessConditions (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V)
    (X : Set V) (β : V →ₗ[K] V →ₗ[K] K) (g : V ≃ₗ[K] V) (c : K) : Prop :=
  F.IsFiniteSymmetric ∧ X.Finite ∧ X.Nonempty ∧
  IsPrimitiveAxialAlgebra F μ X ∧ DirectlyIndecomposable μ ∧
  β ≠ 0 ∧ (∀ u v, β u v = β v u) ∧ IsFrobeniusForm μ β ∧
  IsAlgebraAutomorphism μ g ∧ c ≠ 0 ∧ c ≠ 1 ∧
  (∀ u v, β (g u) (g v) = c * β u v) ∧
  ((∀ u, g (g u) = u) ∨ (∀ u, g (g (g u)) = u))
end General

/-- The dimension bound belongs to the assigned search ansatz. -/
def ExampleOver (K : Type*) [Field K] : Prop :=
  ∃ (n : ℕ) (T : Fin n → Fin n → (Fin n → K)) (F : FusionLaw K)
    (X : Set (Fin n → K)) (β : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K)
    (g : (Fin n → K) ≃ₗ[K] (Fin n → K)) (c : K),
    2 ≤ n ∧ n ≤ 8 ∧ WitnessConditions F (structProduct T) X β g c

def StrongExampleOver (K : Type*) [Field K] : Prop :=
  ∃ (n : ℕ) (T : Fin n → Fin n → (Fin n → K)) (F : FusionLaw K)
    (X : Set (Fin n → K)) (β : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K)
    (g : (Fin n → K) ≃ₗ[K] (Fin n → K)) (c : K),
    2 ≤ n ∧ n ≤ 8 ∧ WitnessConditions F (structProduct T) X β g c ∧
    FormSpaceOneDimensional (structProduct T) β ∧ HasNoIdentity (structProduct T)

/-- A full affirmative answer, in one of the concrete permitted search fields. -/
def ShpectorovAnswer : Prop :=
  ExampleOver ℚ ∨ ExampleOver (ZMod 5) ∨ ExampleOver (ZMod 7) ∨ ExampleOver (ZMod 11)

/-- Optional stronger answer to the explicitly preferred one-dimensional case. -/
def StrongShpectorovAnswer : Prop :=
  StrongExampleOver ℚ ∨ StrongExampleOver (ZMod 5) ∨ StrongExampleOver (ZMod 7) ∨ StrongExampleOver (ZMod 11)
end TaskG.Challenge
