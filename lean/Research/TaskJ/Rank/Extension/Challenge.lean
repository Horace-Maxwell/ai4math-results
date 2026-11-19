import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.PNat.Basic

/-!
A finite cyclic group acts by simultaneous translations on a disjoint union
of cyclic sets. All Weyl groups used for the paper's packets below are actual
quotient groups of this acting group by the corresponding stabilizers.
-/
namespace TaskJ.Rank.Extension

noncomputable section
open scoped Classical

structure Family (n : ℕ) where
  modulus : ℕ+
  width : Fin n → ℕ+
  divides : ∀ i, (width i : ℕ) ∣ (modulus : ℕ)

namespace Family

variable {n : ℕ}

abbrev Actor (D : Family n) := Multiplicative (ZMod (D.modulus : ℕ))
abbrev Fiber (D : Family n) (i : Fin n) := Multiplicative (ZMod (D.width i : ℕ))
abbrev Point (D : Family n) := Σ i : Fin n, D.Fiber i

def projection (D : Family n) (i : Fin n) : D.Actor →* D.Fiber i :=
  (ZMod.castHom (D.divides i) (ZMod (D.width i : ℕ))).toAddMonoidHom.toMultiplicative

def shift (D : Family n) (g : D.Actor) : Equiv.Perm D.Point :=
  Equiv.sigmaCongrRight (fun i => Equiv.mulLeft (D.projection i g))

def action (D : Family n) : D.Actor →* Equiv.Perm D.Point where
  toFun := D.shift
  map_one' := by
    apply Equiv.ext
    rintro ⟨i,x⟩
    change Sigma.mk i (D.projection i 1 * x) = Sigma.mk i x
    rw [map_one, one_mul]
  map_mul' g h := by
    apply Equiv.ext
    rintro ⟨i,x⟩
    change Sigma.mk i (D.projection i (g*h) * x) =
      Sigma.mk i (D.projection i g * (D.projection i h * x))
    rw [map_mul, mul_assoc]

def automorphisms (D : Family n) : Subgroup (Equiv.Perm D.Point) :=
  Subgroup.centralizer (Set.range D.action)

/-- As the actor is abelian all conjugacy classes of stabilizers are singletons. -/
def stabilizer (D : Family n) (x : D.Point) : Subgroup D.Actor :=
  MulAction.stabilizer (Equiv.Perm D.Point) x |>.comap D.action

def boxGroup (D : Family n) (i : Fin n) : Subgroup D.Actor := D.stabilizer ⟨i,1⟩

/-- The actor normalizes every subgroup, so G/H is exactly N_G(H)/H. -/
abbrev Weyl (D : Family n) (i : Fin n) := D.Actor ⧸ D.boxGroup i

def orbit (D : Family n) (x : D.Point) : Set D.Point :=
  Set.range (fun g : D.Actor => D.action g x)

def boxes (D : Family n) : Set (Subgroup D.Actor) := Set.range D.stabilizer

def orbitsInBox (D : Family n) (H : Subgroup D.Actor) : Set (Set D.Point) :=
  Set.range (fun x : {v : D.Point // D.stabilizer v = H} => D.orbit x.val)

def r (D : Family n) : ℕ := Nat.card D.boxes

def kappa (D : Family n) : ℕ :=
  Nat.card {H : D.boxes // Nat.card (D.orbitsInBox H.val) = 1}

def capitalLambda (D : Family n) : ℕ :=
  if (D.r = D.kappa ∧ ∀ H : D.boxes, Subsingleton (D.Actor ⧸ H.val)) ∨
    (∃ H : D.boxes, 3 ≤ Nat.card (D.orbitsInBox H.val)) then 1 else 0

abbrev Bases (D : Family n) := ∀ i, Finset (D.Weyl i)

/-- Both sources use nonempty generating sets for the trivial Weyl group. -/
def Valid (D : Family n) (B : D.Bases) : Prop :=
  ∀ i, Subgroup.closure (B i : Set (D.Weyl i)) = ⊤ ∧
    (B i).card = max 1 (Group.rank (D.Weyl i))

abbrev Item (D : Family n) (B : D.Bases) :=
  Σ i, {g : D.Weyl i // g ∈ B i ∧ g ≠ 1}

/-- Colors label packets. Unused labels do not affect the minimum. The order
of a Weyl element is the order of its translation on its representative orbit. -/
def Fits (D : Family n) (B : D.Bases) (k : ℕ) : Prop :=
  ∃ f : D.Item B → Fin k, ∀ x y, x ≠ y → f x = f y →
    x.1 ≠ y.1 ∧ Nat.Coprime (orderOf x.2.val) (orderOf y.2.val)

def packets (D : Family n) (B : D.Bases) : ℕ := sInf {k : ℕ | D.Fits B k}

def preprint (D : Family n) (B : D.Bases) : ℤ :=
  (D.r : ℤ) - D.kappa + D.capitalLambda + D.packets B

def journal (D : Family n) (B : D.Bases) : ℤ := D.preprint B + 1

end Family

/-- Both papers' predicted ranks grow without bound while the actual group
rank stays two. The conclusion holds for *every* allowable minimal basis. -/
def UnboundedGap : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ D : Family n,
    (∀ i, 1 < (D.width i : ℕ)) ∧ Function.Injective D.width ∧
    Function.Injective D.action ∧ IsCyclic D.Actor ∧
    (∀ x : D.Point, D.stabilizer x = (D.projection x.1).ker) ∧
    (∀ x : D.Point, D.orbit x = {y | y.1 = x.1}) ∧
    Function.Injective D.boxGroup ∧
    (∀ i, Nonempty (D.Weyl i ≃* D.Fiber i)) ∧
    D.r = n ∧ D.kappa = n ∧ D.capitalLambda = 0 ∧
    Group.rank D.automorphisms = 2 ∧ (∃ B : D.Bases, D.Valid B) ∧
    ∀ B : D.Bases, D.Valid B → D.packets B = n ∧
      D.preprint B = (n : ℤ) ∧ D.journal B = (n : ℤ) + 1

end
end TaskJ.Rank.Extension
