import Research.Backfill.Paper7.MomentB4FixedTypeFiniteSums

/-! NEW SOURCE ONLY. Exact small blocks of the sealed finite sums.
All outer indices remain in the assembly. No numerical block table or
total-cardinality hypothesis is introduced. Imports remain pending. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge.Legacy Paper7MomentCertificate
open scoped BigOperators Classical

def b4Type22Block (z t : Fin 19) : ℕ :=
  ∑ R : Fin 10, if type22Accept (z,t,R) then
    min z.val R.val+1-(R.val-t.val) else 0
#print axioms Paper7MomentCanonicalNumeric.b4Type22Block

def b4Type112Block (z : Fin 38) (t : Fin 19) (u : Fin 38) : ℕ :=
  ∑ Q : Fin 19, if B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val then
    b4Type112RowWeight (z,t,u,Q) else 0
#print axioms Paper7MomentCanonicalNumeric.b4Type112Block

theorem b4_type22_finite_sum_eq_blocks :
    b4Type22FiniteSum = ∑ z : Fin 19, ∑ t : Fin 19, b4Type22Block z t := by
  simp only [b4Type22FiniteSum,b4Type22Block,Fintype.sum_prod_type]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_finite_sum_eq_blocks

theorem b4_type112_finite_sum_eq_blocks :
    b4Type112FiniteSum =
      ∑ z : Fin 38, ∑ t : Fin 19, ∑ u : Fin 38, b4Type112Block z t u := by
  rw [b4_type112_finite_sum_by_catalog_rows]
  simp only [b4Type112Block,Fintype.sum_prod_type]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_finite_sum_eq_blocks

theorem b4_canonical_clauses_iff_block_sums :
    ((canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641) ∧
      ((canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641) ↔
        3*(∑ z : Fin 19, ∑ t : Fin 19, b4Type22Block z t)+
          2*(∑ z : Fin 38, ∑ t : Fin 19, ∑ u : Fin 38, b4Type112Block z t u) = 10584 := by
  rw [b4_canonical_clauses_iff_two_finite_sums,
    b4_type22_finite_sum_eq_blocks,b4_type112_finite_sum_eq_blocks]
#print axioms Paper7MomentCanonicalNumeric.b4_canonical_clauses_iff_block_sums

end Paper7MomentCanonicalNumeric
