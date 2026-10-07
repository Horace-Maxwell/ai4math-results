import Research.Backfill.Paper5.Challenge

set_option autoImplicit false

universe u v

namespace CodexPaper5.AssociativityStatement

open BackfillPaper5

/-- A graph replacement preserves reachability between every retained pair,
including after any additional graph whose edges stay in the retained image.
This is a separate statement contract; no proof is supplied here. -/
def ReachableElimination : Prop :=
  ∀ (V : Type u) (W : Type v) (f : W ↪ V) (G : SimpleGraph V)
    (C H : SimpleGraph W),
    (∀ p q : W, G.Reachable (f p) (f q) ↔ C.Reachable p q) →
    ∀ p q : W,
      (G ⊔ H.map f).Reachable (f p) (f q) ↔ (C ⊔ H).Reachable p q

/-- The actual two bracketed stacks have the same outer connectivity.
All points, all legal partial Brauer diagrams, and n = 0 are included. -/
def OuterBracketReachability : Prop :=
  ∀ (n : ℕ) (x y z : Challenge.Pt n → Challenge.Pt n),
    Challenge.IsPB x → Challenge.IsPB y → Challenge.IsPB z →
    ∀ p q : Challenge.Pt n,
      (Challenge.stackGraph (Challenge.dmul x y) z).Reachable
        (Challenge.outer p) (Challenge.outer q) ↔
      (Challenge.stackGraph x (Challenge.dmul y z)).Reachable
        (Challenge.outer p) (Challenge.outer q)

/-- Associativity of the frozen list-search diagram product on all PB diagrams.
There is no positive-size, rank, or nonempty hypothesis. -/
def PBAssociativity : Prop :=
  ∀ (n : ℕ) (x y z : Challenge.Pt n → Challenge.Pt n),
    Challenge.IsPB x → Challenge.IsPB y → Challenge.IsPB z →
    Challenge.dmul (Challenge.dmul x y) z =
      Challenge.dmul x (Challenge.dmul y z)

/-- The same operation on B; its future proof is obtained from PBAssociativity. -/
def BAssociativity : Prop :=
  ∀ (n : ℕ) (x y z : Challenge.Pt n → Challenge.Pt n),
    x ∈ Challenge.B n → y ∈ Challenge.B n → z ∈ Challenge.B n →
    Challenge.dmul (Challenge.dmul x y) z =
      Challenge.dmul x (Challenge.dmul y z)

/-- An actual Monoid on the frozen PB carrier, with its multiplication and unit
explicitly aligned to dmul and idD. Existence is a goal, not an assumption. -/
def PBMonoidAligned : Prop :=
  ∀ n : ℕ, ∃ M : Monoid ↥(Challenge.Dset Challenge.Fam.PB n),
    (∀ x y : ↥(Challenge.Dset Challenge.Fam.PB n),
      (@Mul.mul ↥(Challenge.Dset Challenge.Fam.PB n) M.toMul x y).val =
        Challenge.dmul x.val y.val) ∧
    (@One.one ↥(Challenge.Dset Challenge.Fam.PB n) M.toOne).val = Challenge.idD n

/-- The corresponding actual B carrier and the same frozen operation/unit. -/
def BMonoidAligned : Prop :=
  ∀ n : ℕ, ∃ M : Monoid ↥(Challenge.Dset Challenge.Fam.B n),
    (∀ x y : ↥(Challenge.Dset Challenge.Fam.B n),
      (@Mul.mul ↥(Challenge.Dset Challenge.Fam.B n) M.toMul x y).val =
        Challenge.dmul x.val y.val) ∧
    (@One.one ↥(Challenge.Dset Challenge.Fam.B n) M.toOne).val = Challenge.idD n

end CodexPaper5.AssociativityStatement

#print axioms CodexPaper5.AssociativityStatement.ReachableElimination
#print axioms CodexPaper5.AssociativityStatement.OuterBracketReachability
#print axioms CodexPaper5.AssociativityStatement.PBAssociativity
#print axioms CodexPaper5.AssociativityStatement.BAssociativity
#print axioms CodexPaper5.AssociativityStatement.PBMonoidAligned
#print axioms CodexPaper5.AssociativityStatement.BMonoidAligned
