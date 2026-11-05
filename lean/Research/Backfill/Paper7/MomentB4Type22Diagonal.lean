import Research.Backfill.Paper7.MomentB4FixedTypeTriangleSlices

/-! SOURCE ONLY. The full Type22 diagonal is a small kernel certificate,
not a sample of a table. All 19 diagonal row parameters and all 10 R values
remain quantified. The full original catalogue predicate is retained. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge.Legacy Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type22_diagonal_accept_iff (z : Fin 19) (R : Fin 10) :
    type22Accept (z,z,R) ↔ z = 3 ∧ R = 3 := by
  have hc : ∀ z : Fin 19, ∀ R : Fin 10,
      type22Accept (z,z,R) ↔ z = 3 ∧ R = 3 := by
    simp only [type22Accept,B4CatalogRowAccept,type22Row,b4Theta,Fin.sum_univ_four]
    decide +kernel
  exact hc z R
#print axioms Paper7MomentCanonicalNumeric.type22_diagonal_accept_iff

theorem b4_type22_diagonal_block (z : Fin 19) :
    b4Type22Block z z = if z = 3 then 4 else 0 := by
  unfold b4Type22Block
  simp_rw [type22_diagonal_accept_iff]
  by_cases hz : z = 3
  · subst z
    norm_num
  · simp [hz]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_diagonal_block

theorem b4_type22_diagonal_sum :
    (∑ z : Fin 19, b4Type22Block z z) = 4 := by
  simp_rw [b4_type22_diagonal_block]
  simp
#print axioms Paper7MomentCanonicalNumeric.b4_type22_diagonal_sum

theorem b4_type22_diagonal_budget_sum :
    (∑ z ∈ (Finset.univ : Finset (Fin 19)).filter (fun z => 2*z.val ≤ 18),
      b4Type22Block z z) = 4 := by
  rw [Finset.sum_filter]
  simp_rw [b4_type22_diagonal_block]
  have h (z : Fin 19) :
      (if 2*z.val ≤ 18 then (if z = 3 then 4 else 0) else 0) =
        if z = 3 then 4 else 0 := by
    by_cases hz : z = 3
    · subst z
      norm_num
    · simp [hz]
  simp_rw [h]
  simp
#print axioms Paper7MomentCanonicalNumeric.b4_type22_diagonal_budget_sum

def b4Type22StrictTriangleTotal : ℕ :=
  ∑ z : Fin 19, ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter
    (fun t => z < t ∧ z.val+t.val ≤ 18), b4Type22Block z t
#print axioms Paper7MomentCanonicalNumeric.b4Type22StrictTriangleTotal

theorem b4_type22_finite_sum_eq_four_add_twice_triangle :
    b4Type22FiniteSum = 4 + 2*b4Type22StrictTriangleTotal := by
  rw [b4_type22_finite_sum_eq_triangular_budget,b4_type22_diagonal_budget_sum]
  rfl
#print axioms Paper7MomentCanonicalNumeric.b4_type22_finite_sum_eq_four_add_twice_triangle

theorem b4_canonical_clauses_iff_diagonal_removed :
    ((canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641) ∧
      ((canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641) ↔
        3*b4Type22StrictTriangleTotal+b4Type112FiniteSum = 5286 := by
  rw [b4_canonical_clauses_iff_two_finite_sums,
    b4_type22_finite_sum_eq_four_add_twice_triangle]
  omega
#print axioms Paper7MomentCanonicalNumeric.b4_canonical_clauses_iff_diagonal_removed

end Paper7MomentCanonicalNumeric
