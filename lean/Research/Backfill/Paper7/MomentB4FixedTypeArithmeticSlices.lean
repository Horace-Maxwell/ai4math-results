import Research.Backfill.Paper7.MomentB4FixedTypeBlocks
import Research.Backfill.Paper7.MomentB4RowSymmetry

/-! SOURCE ONLY. Cheap necessary arithmetic guards are proved from the
original catalogue predicate before any fixed-type fibre is counted.
Every original outer index remains in the two exact assembly equalities.
The numerical equality 10584 is not proved or assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge.Legacy Paper7MomentCounts Paper7MomentCertificate
open Paper7MomentReduction
open scoped BigOperators Classical

def b4RowArithmeticGuard (z : Fin 4 → ℕ) (Q : ℕ) : Prop :=
  Q ≤ (∑ i, z i) ∧ 0 < (∑ i, z i) + Q ∧ 4 + ((∑ i, z i) + Q) ≤ 41 ∧
    b4Theta z Q + 4 ≤ 1272 ∧ (b4Theta z Q + 4) % 12 = 0
#print axioms Paper7MomentCanonicalNumeric.b4RowArithmeticGuard

theorem b4_catalog_implies_arithmetic_guard (z : Fin 4 → ℕ) (Q : ℕ)
    (h : B4CatalogRowAccept z Q) : b4RowArithmeticGuard z Q := by
  rcases h with ⟨hQ,hp,hn,⟨S,M⟩,hm,heq,_hlo,_hhi⟩
  refine ⟨hQ,hp,hn,?_⟩
  have hb : M ≤ 1272 ∧ M % 12 = 0 := b4_catalog_fourth_bounds S M hm
  change M = b4Theta z Q + 4 at heq
  exact heq ▸ hb
#print axioms Paper7MomentCanonicalNumeric.b4_catalog_implies_arithmetic_guard

def b4Type22ArithmeticDomain (z t : Fin 19) : Finset (Fin 10) :=
  Finset.univ.filter (fun R => b4RowArithmeticGuard (type22Row (z,t,R)) (2*R.val))
#print axioms Paper7MomentCanonicalNumeric.b4Type22ArithmeticDomain

def b4Type112ArithmeticDomain (z : Fin 38) (t : Fin 19) (u : Fin 38) :
    Finset (Fin 19) :=
  Finset.univ.filter (fun Q => b4RowArithmeticGuard (type112Row (z,t,u,Q)) Q.val)
#print axioms Paper7MomentCanonicalNumeric.b4Type112ArithmeticDomain

theorem b4_type22_block_eq_arithmetic_slice (z t : Fin 19) :
    b4Type22Block z t = ∑ R ∈ b4Type22ArithmeticDomain z t,
      if type22Accept (z,t,R) then min z.val R.val+1-(R.val-t.val) else 0 := by
  unfold b4Type22Block b4Type22ArithmeticDomain
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro R _
  by_cases ha : type22Accept (z,t,R)
  · have hg := b4_catalog_implies_arithmetic_guard (type22Row (z,t,R)) (2*R.val) ha
    simp only [ite_eq_left ha,ite_eq_left hg]
  · simp only [ite_eq_right ha,ite_self]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_block_eq_arithmetic_slice

theorem b4_type112_block_eq_arithmetic_slice (z : Fin 38) (t : Fin 19) (u : Fin 38) :
    b4Type112Block z t u = ∑ Q ∈ b4Type112ArithmeticDomain z t u,
      if B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val then
        b4Type112RowWeight (z,t,u,Q) else 0 := by
  unfold b4Type112Block b4Type112ArithmeticDomain
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases ha : B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val
  · have hg := b4_catalog_implies_arithmetic_guard (type112Row (z,t,u,Q)) Q.val ha
    simp only [ite_eq_left ha,ite_eq_left hg]
  · simp only [ite_eq_right ha,ite_self]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_block_eq_arithmetic_slice

theorem b4_type22_finite_sum_eq_arithmetic_slices :
    b4Type22FiniteSum = ∑ z : Fin 19, ∑ t : Fin 19,
      ∑ R ∈ b4Type22ArithmeticDomain z t,
        if type22Accept (z,t,R) then min z.val R.val+1-(R.val-t.val) else 0 := by
  rw [b4_type22_finite_sum_eq_blocks]
  simp_rw [b4_type22_block_eq_arithmetic_slice]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_finite_sum_eq_arithmetic_slices

theorem b4_type112_finite_sum_eq_arithmetic_slices :
    b4Type112FiniteSum = ∑ z : Fin 38, ∑ t : Fin 19, ∑ u : Fin 38,
      ∑ Q ∈ b4Type112ArithmeticDomain z t u,
        if B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val then
          b4Type112RowWeight (z,t,u,Q) else 0 := by
  rw [b4_type112_finite_sum_eq_blocks]
  simp_rw [b4_type112_block_eq_arithmetic_slice]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_finite_sum_eq_arithmetic_slices

theorem b4_canonical_clauses_iff_arithmetic_slices :
    ((canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641) ∧
      ((canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641) ↔
        3*(∑ z : Fin 19, ∑ t : Fin 19,
          ∑ R ∈ b4Type22ArithmeticDomain z t,
            if type22Accept (z,t,R) then min z.val R.val+1-(R.val-t.val) else 0)+
        2*(∑ z : Fin 38, ∑ t : Fin 19, ∑ u : Fin 38,
          ∑ Q ∈ b4Type112ArithmeticDomain z t u,
            if B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val then
              b4Type112RowWeight (z,t,u,Q) else 0) = 10584 := by
  rw [b4_canonical_clauses_iff_two_finite_sums,
    b4_type22_finite_sum_eq_arithmetic_slices,b4_type112_finite_sum_eq_arithmetic_slices]
#print axioms Paper7MomentCanonicalNumeric.b4_canonical_clauses_iff_arithmetic_slices

end Paper7MomentCanonicalNumeric
