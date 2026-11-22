import Mathlib

/-! Vojtěchovský–Yang, Conjecture 6.5. Operations use the paper's left convention. -/

namespace TaskP.PrimeMedialRacks.Challenge

abbrev Operation (α : Type*) := α → α → α

def IsRack {α : Type*} (op : Operation α) : Prop :=
  (∀ x, Function.Bijective (op x)) ∧
    ∀ x y z, op x (op y z) = op (op x y) (op x z)

def Idempotent {α : Type*} (op : Operation α) : Prop :=
  ∀ x, op x x = x

def Medial {α : Type*} (op : Operation α) : Prop :=
  ∀ x u v y, op (op x u) (op v y) = op (op x v) (op u y)

/-- The four-variable identity (1.1) from the paper. -/
def TwoReductive {α : Type*} (op : Operation α) : Prop :=
  ∀ x y u v, op (op x u) v = op (op y u) v

def Isomorphic {α β : Type*} (op : Operation α) (op' : Operation β) : Prop :=
  ∃ e : α ≃ β, ∀ x y, e (op x y) = op' (e x) (e y)

/-- Relabel all entries and both inputs of the multiplication table by one permutation. -/
def isoSetoid (n : ℕ) : Setoid (Operation (Fin n)) where
  r := Isomorphic
  iseqv := {
    refl := fun _ => ⟨Equiv.refl _, fun _ _ => rfl⟩
    symm := by
      rintro _ _ ⟨e, h⟩
      refine ⟨e.symm, fun x y => e.injective ?_⟩
      simp [h]
    trans := by
      rintro _ _ _ ⟨e, h⟩ ⟨f, k⟩
      exact ⟨e.trans f, fun x y => by simp [h, k]⟩ }

abbrev IsoClass (n : ℕ) := Quotient (isoSetoid n)

/-- Count those isomorphism classes with a representative satisfying P. Finiteness follows
from the finite set of all binary operations on the fixed n-point carrier. -/
noncomputable def classCount (n : ℕ) (P : Operation (Fin n) → Prop) : ℕ := by
  classical
  let C := {q : IsoClass n // ∃ op, Quotient.mk (isoSetoid n) op = q ∧ P op}
  letI : Fintype C := Fintype.ofFinite C
  exact Fintype.card C

/-- The rack enumeration in additive form, including the prime 2. -/
def RackCount : Prop :=
  ∀ p : ℕ, p.Prime →
    classCount p (fun op => IsRack op ∧ Medial op) =
      classCount p (fun op => IsRack op ∧ TwoReductive op) + (p - 2)

/-- The quandle enumeration, imposing idempotence on both classes. -/
def QuandleCount : Prop :=
  ∀ p : ℕ, p.Prime →
    classCount p (fun op => IsRack op ∧ Idempotent op ∧ Medial op) =
      classCount p (fun op => IsRack op ∧ Idempotent op ∧ TwoReductive op) + (p - 2)

/-- The structural consequence explicitly stated after the two equations. -/
def AutomaticIdempotence : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ op : Operation (Fin p),
    IsRack op → Medial op → ¬ TwoReductive op → Idempotent op

end TaskP.PrimeMedialRacks.Challenge
