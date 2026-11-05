import Research.Backfill.Paper7.MomentB4Type112Fibres
import Research.Backfill.Paper7.MomentB4Type22Fibres

/-! NEW SOURCE ONLY. Catalogue-first exact finite sums for the two original
nonconstant cycle types. The numerical equality 10584 remains a proof goal. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge.Legacy Paper7MomentCertificate
open scoped BigOperators Classical

def b4Type112RowWeight (r : B4Type112RowIndex) : ℕ :=
  ∑ k : Fin 10, if k.val ≤ r.2.1.val ∧ 2*k.val ≤ r.2.2.2.val then
    min r.1.val (r.2.2.2.val-2*k.val)+1-
      ((r.2.2.2.val-2*k.val)-r.2.2.1.val) else 0
#print axioms Paper7MomentCanonicalNumeric.b4Type112RowWeight

theorem b4_type112_finite_sum_by_catalog_rows :
    b4Type112FiniteSum = ∑ r : B4Type112RowIndex,
      if B4CatalogRowAccept (type112Row r) r.2.2.2.val then b4Type112RowWeight r else 0 := by
  rw [b4Type112FiniteSum,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  by_cases ha : B4CatalogRowAccept (type112Row r) r.2.2.2.val
  · simp only [type112Accept,ha,and_true,ite_true,b4Type112RowWeight,type112Residual]
  · simp [type112Accept,ha]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_finite_sum_by_catalog_rows

theorem b4_canonical_clauses_iff_two_finite_sums :
    ((canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641) ∧
      ((canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641) ↔
        3*b4Type22FiniteSum+2*b4Type112FiniteSum = 10584 := by
  rw [b4_canonical_clauses_iff_two_types,b4_type22_card_eq_finite_sum,
    b4_type112_card_eq_finite_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_canonical_clauses_iff_two_finite_sums

end Paper7MomentCanonicalNumeric
