import Research.Backfill.Paper5.Challenge

set_option autoImplicit false

namespace CodexPaper5.FullPaperStatement

open BackfillPaper5

/-- The complete whole-monoid classification in every degree, including zero. -/
def AllNClassification : Prop :=
  ∀ n : ℕ,
    (Challenge.SubsetHasCM Challenge.dmul (Challenge.B n) ↔
      Challenge.SubsetHasCM Challenge.dmul (Challenge.PB n)) ∧
    (Challenge.SubsetHasCM Challenge.dmul (Challenge.PB n) ↔
      Challenge.HasCM (Challenge.Sym n)) ∧
    (Challenge.HasCM (Challenge.Sym n) ↔ n ≠ 2 ∧ n ≠ 3)

/-- Actual diagrams of fixed rank whose two halves are the specified same half. -/
abbrev Corner (D : Challenge.Fam) (n r : ℕ) (l : Challenge.Half n) :=
  {x : Challenge.Pt n → Challenge.Pt n //
    x ∈ Challenge.Jr D n r ∧ Challenge.topHalf x = l ∧ Challenge.botHalf x = l}

/-- A genuine group on the actual carrier and a genuine multiplicative equivalence.
Its product, identity and coordinate map are the frozen actual diagram operations. -/
def CornerGroupAligned : Prop :=
  ∀ (D : Challenge.Fam) (n r : ℕ) (l : Challenge.Half n),
    l ∈ Challenge.Hr D n r →
    ∃ M : Group (Corner D n r l),
      letI : Group (Corner D n r l) := M
      ∃ e : Corner D n r l ≃* Challenge.Sym r,
        (∀ x y : Corner D n r l,
          (x * y).val = Challenge.dmul x.val y.val) ∧
        (1 : Corner D n r l).val = Challenge.eDiag l ∧
        (∀ x : Corner D n r l, e x = Challenge.gCoord r x.val)

end CodexPaper5.FullPaperStatement

#print axioms CodexPaper5.FullPaperStatement.AllNClassification
#print axioms CodexPaper5.FullPaperStatement.Corner
#print axioms CodexPaper5.FullPaperStatement.CornerGroupAligned
