import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
The two witnesses specialize both sources to C₂ = ℤ/2. Stabilizers are subsets
of this actual acting group. It is abelian, so each stabilizer is its own
conjugacy class and has the whole group as normalizer. The cosets below are
the elements of its Weyl quotient, with the induced addition.
-/
namespace TaskJ.Rank.Challenge

abbrev C2 := ZMod 2
abbrev Box := Finset C2
abbrev Coset := Finset C2
abbrev BaseItem := Box × Coset

def twoSwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

def fiveSwap : Equiv.Perm (Fin 5) := Equiv.swap 0 1

def act {n : ℕ} (t : Equiv.Perm (Fin n)) (g : C2) (x : Fin n) : Fin n :=
  if g = 0 then x else t x

def ActionLaws {n : ℕ} (t : Equiv.Perm (Fin n)) : Prop :=
  (∀ x, act t 0 x = x) ∧ (∀ g h x, act t (g + h) x = act t g (act t h x))

def equivariantGroup {n : ℕ} (t : Equiv.Perm (Fin n)) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.centralizer ({t} : Set _)

def EquivarianceMeaning {n : ℕ} (t : Equiv.Perm (Fin n)) : Prop :=
  ∀ p : Equiv.Perm (Fin n), p ∈ equivariantGroup t ↔
    ∀ (g : C2) (x : Fin n), p (act t g x) = act t g (p x)

def stabilizer {n : ℕ} (t : Equiv.Perm (Fin n)) (x : Fin n) : Box :=
  Finset.univ.filter fun g => act t g x = x

def orbit {n : ℕ} (t : Equiv.Perm (Fin n)) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.image fun g : C2 => act t g x

def boxes {n : ℕ} (t : Equiv.Perm (Fin n)) : Finset Box :=
  Finset.univ.image (stabilizer t)

def orbitsInBox {n : ℕ} (t : Equiv.Perm (Fin n)) (H : Box) : Finset (Finset (Fin n)) :=
  (Finset.univ.filter fun x => stabilizer t x = H).image (orbit t)

def coset (H : Box) (g : C2) : Coset := H.image fun h => g + h

def weyl (H : Box) : Finset Coset := Finset.univ.image (coset H)

def cosetAdd (a b : Coset) : Coset := a.biUnion fun x => b.image fun y => x + y

/-- Subgroups of this finite Weyl quotient are exactly the subsets containing
zero and closed under addition (in C₂ every coset is its own inverse). -/
def weylSubgroups (H : Box) : Finset (Finset Coset) :=
  (weyl H).powerset.filter fun S =>
    H ∈ S ∧ ∀ a ∈ S, ∀ b ∈ S, cosetAdd a b ∈ S

/-- Both papers require the trivial group to have rank one. Nonempty
generating sets give this convention also on the trivial Weyl quotient. -/
def authorGeneratingSets (H : Box) : Finset (Finset Coset) :=
  (weyl H).powerset.filter fun S =>
    S.Nonempty ∧ ∀ K ∈ weylSubgroups H, S ⊆ K → K = weyl H

/-- Least cardinality occurring in a finite family of subsets with sizes
bounded by b. The b+1 sentinel applies only to an empty search. -/
def minimumSize {α : Type} [DecidableEq α] (family : Finset (Finset α)) (b : ℕ) : ℕ :=
  ((List.range (b + 1)).find? fun k => decide (∃ s ∈ family, s.card = k)).getD (b + 1)

def weylRank (H : Box) : ℕ := minimumSize (authorGeneratingSets H) (weyl H).card

/-- In a quotient of C₂, the nonzero group element maps to a generator;
on the trivial quotient this is the identity, retained only in the rank sum.
The two concrete contracts check this choice is a minimum generating set. -/
def selectedBasis (H : Box) : Finset Coset := {coset H 1}

def BasesValid {n : ℕ} (t : Equiv.Perm (Fin n)) : Prop :=
  ∀ H ∈ boxes t, selectedBasis H ∈ authorGeneratingSets H ∧
    (selectedBasis H).card = weylRank H

def cosetMultiple (H : Box) (a : Coset) : ℕ → Coset
  | 0 => H
  | k + 1 => cosetAdd (cosetMultiple H a k) a

def cosetOrder (H : Box) (a : Coset) : ℕ :=
  ((List.range ((weyl H).card + 1)).find? fun k =>
    decide (0 < k ∧ cosetMultiple H a k = H)).getD ((weyl H).card + 1)

def baseItems {n : ℕ} (t : Equiv.Perm (Fin n)) : Finset BaseItem :=
  (boxes t).biUnion fun H =>
    ((selectedBasis H).filter fun a => 1 < cosetOrder H a).image (Prod.mk H)

/-- The order of the orbit-supported lift of a Weyl element equals its order
in that quotient: on its representative orbit it acts by translation. -/
def legalPacket (P : Finset BaseItem) : Bool :=
  decide (P.Nonempty ∧ ∀ i ∈ P, ∀ j ∈ P, i ≠ j →
    i.1 ≠ j.1 ∧ Nat.Coprime (cosetOrder i.1 i.2) (cosetOrder j.1 j.2))

def separated (P Q : Finset BaseItem) : Bool :=
  (P == Q) || ((P ∩ Q) == ∅)

def disjointFromOthers (Q : Finset (Finset BaseItem)) (P : Finset BaseItem) : Bool :=
  (Q.filter fun R => separated P R = false).card == 0

def isPacketPartition (B : Finset BaseItem) (Q : Finset (Finset BaseItem)) : Bool :=
  (Q.biUnion id == B) &&
    ((Q.filter fun P => legalPacket P = false).card == 0) &&
    ((Q.filter fun P => disjointFromOthers Q P = false).card == 0)

def packetPartitions (B : Finset BaseItem) : Finset (Finset (Finset BaseItem)) :=
  B.powerset.powerset.filter fun Q => isPacketPartition B Q = true

def packetNumber {n : ℕ} (t : Equiv.Perm (Fin n)) : ℕ :=
  minimumSize (packetPartitions (baseItems t)) (baseItems t).card

def r {n : ℕ} (t : Equiv.Perm (Fin n)) : ℕ := (boxes t).card

def kappa {n : ℕ} (t : Equiv.Perm (Fin n)) : ℕ :=
  ((boxes t).filter fun H => (orbitsInBox t H).card = 1).card

def omega {n : ℕ} (t : Equiv.Perm (Fin n)) : ℕ :=
  ((boxes t).filter fun H => (weyl H).card = 1).card

def rankSum {n : ℕ} (t : Equiv.Perm (Fin n)) : ℕ :=
  ∑ H ∈ boxes t, weylRank H

def capitalLambda {n : ℕ} (t : Equiv.Perm (Fin n)) : ℕ :=
  if (r t = kappa t ∧ ∀ H ∈ boxes t, (weyl H).card = 1) ∨
      (∃ H ∈ boxes t, 3 ≤ (orbitsInBox t H).card) then 1 else 0

def deltaDisplayed {n : ℕ} (t : Equiv.Perm (Fin n)) : ℕ :=
  if omega t = rankSum t then 0 else 1

/-- Printed expressions use ordinary integer subtraction throughout. -/
def firstBound {n : ℕ} (t : Equiv.Perm (Fin n)) : ℤ :=
  (r t : ℤ) - kappa t + capitalLambda t - omega t - deltaDisplayed t + rankSum t

def preprintPacketBound {n : ℕ} (t : Equiv.Perm (Fin n)) : ℤ :=
  (r t : ℤ) - kappa t + capitalLambda t + packetNumber t

def journalPacketBound {n : ℕ} (t : Equiv.Perm (Fin n)) : ℤ := preprintPacketBound t + 1

def TwoPointParameters : Prop :=
  r twoSwap = 1 ∧ kappa twoSwap = 1 ∧ capitalLambda twoSwap = 0 ∧
  omega twoSwap = 0 ∧ rankSum twoSwap = 1 ∧ deltaDisplayed twoSwap = 1 ∧
  packetNumber twoSwap = 1 ∧ firstBound twoSwap = 0 ∧
  preprintPacketBound twoSwap = 1 ∧ journalPacketBound twoSwap = 2

def FivePointParameters : Prop :=
  r fiveSwap = 2 ∧ kappa fiveSwap = 1 ∧ capitalLambda fiveSwap = 1 ∧
  omega fiveSwap = 1 ∧ rankSum fiveSwap = 2 ∧ deltaDisplayed fiveSwap = 1 ∧
  packetNumber fiveSwap = 1 ∧ firstBound fiveSwap = 2 ∧
  preprintPacketBound fiveSwap = 3 ∧ journalPacketBound fiveSwap = 4

def TwoPointRank : Prop := Group.rank (equivariantGroup twoSwap) = 1
def FivePointRank : Prop := Group.rank (equivariantGroup fiveSwap) = 2

def TwoPointCounterexample : Prop :=
  ActionLaws twoSwap ∧ EquivarianceMeaning twoSwap ∧ BasesValid twoSwap ∧
  TwoPointParameters ∧ TwoPointRank ∧
  ¬ ((Group.rank (equivariantGroup twoSwap) : ℤ) ≤ firstBound twoSwap)

def FivePointCounterexample : Prop :=
  ActionLaws fiveSwap ∧ EquivarianceMeaning fiveSwap ∧ BasesValid fiveSwap ∧
  FivePointParameters ∧ FivePointRank ∧
  (Group.rank (equivariantGroup fiveSwap) : ℤ) < preprintPacketBound fiveSwap ∧
  (Group.rank (equivariantGroup fiveSwap) : ℤ) < journalPacketBound fiveSwap

end TaskJ.Rank.Challenge
