import Research.Backfill.Paper5.Challenge

set_option autoImplicit false

universe u v w

namespace CodexPaper5.AlgebraStatement

open BackfillPaper5

/-- The frozen actual Rees multiplication is associative whenever the base is a semigroup.
No restrictions on the index sets or the zero pattern of the sandwich matrix. -/
def ReesAssociativity : Prop :=
  ∀ (G : Type u) (I : Type v) (L : Type w)
    (M : Semigroup G) (P : L → I → Option G),
    letI : Semigroup G := M
    ∀ x y z : Challenge.Rees0 G I L,
      Challenge.rees0Mul P (Challenge.rees0Mul P x y) z =
        Challenge.rees0Mul P x (Challenge.rees0Mul P y z)

/-- A transversal is an actual subset of the table cells, with bijective row,
column and multiplication-value projections; even an empty magma is allowed. -/
def CayleyTransversalIff : Prop :=
  ∀ (S : Type u) (op : S → S → S),
    (∃ a : S → S, Challenge.IsCompleteMapping op a) ↔
      ∃ T : Set (S × S),
        Function.Bijective (fun x : T => x.val.1) ∧
        Function.Bijective (fun x : T => x.val.2) ∧
        Function.Bijective (fun x : T => op x.val.1 x.val.2)

/-- The first concrete odd half-count retained in the manuscript. -/
def HalfCount45 : Prop := (Challenge.Hr Challenge.Fam.B 6 2).ncard = 45

/-- The second concrete odd half-count retained in the manuscript. -/
def HalfCount105 : Prop := (Challenge.Hr Challenge.Fam.B 7 3).ncard = 105

end CodexPaper5.AlgebraStatement

#print axioms CodexPaper5.AlgebraStatement.ReesAssociativity
#print axioms CodexPaper5.AlgebraStatement.CayleyTransversalIff
#print axioms CodexPaper5.AlgebraStatement.HalfCount45
#print axioms CodexPaper5.AlgebraStatement.HalfCount105
