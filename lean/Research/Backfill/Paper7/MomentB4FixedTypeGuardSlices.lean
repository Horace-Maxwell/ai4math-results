import Research.Backfill.Paper7.MomentB4FixedTypeBlocks

/-! NEW SOURCE ONLY, UNCOMPILED. Exact guard slices of both original fixed-type
finite sums. Only the original Q and order guards are used. No catalogue
expansion, numerical block table, total-cardinality premise or set equality
between canonB1 and canonD2 is introduced. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCertificate
open scoped BigOperators Classical

theorem type22_accept_budget (z t : Fin 19) (R : Fin 10)
    (h : type22Accept (z,t,R)) : z.val+t.val+R.val ≤ 18 := by
  have hb := h.2.2.1
  rw [Fin.sum_univ_four] at hb
  change 4+(z.val+t.val+z.val+t.val+2*R.val) ≤ 41 at hb
  omega
#print axioms Paper7MomentCanonicalNumeric.type22_accept_budget

theorem type22_accept_q_le (z t : Fin 19) (R : Fin 10)
    (h : type22Accept (z,t,R)) : R.val ≤ z.val+t.val := by
  have hq := h.1
  rw [Fin.sum_univ_four] at hq
  change 2*R.val ≤ z.val+t.val+z.val+t.val at hq
  omega
#print axioms Paper7MomentCanonicalNumeric.type22_accept_q_le

theorem type112_accept_budget (z : Fin 38) (t : Fin 19) (u : Fin 38) (Q : Fin 19)
    (h : B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val) :
    z.val+2*t.val+u.val+Q.val ≤ 37 := by
  have hb := h.2.2.1
  rw [Fin.sum_univ_four] at hb
  change 4+(z.val+t.val+u.val+t.val+Q.val) ≤ 41 at hb
  omega
#print axioms Paper7MomentCanonicalNumeric.type112_accept_budget

theorem type112_accept_q_le (z : Fin 38) (t : Fin 19) (u : Fin 38) (Q : Fin 19)
    (h : B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val) :
    Q.val ≤ z.val+2*t.val+u.val := by
  have hq := h.1
  rw [Fin.sum_univ_four] at hq
  change Q.val ≤ z.val+t.val+u.val+t.val at hq
  omega
#print axioms Paper7MomentCanonicalNumeric.type112_accept_q_le

theorem b4_type22_block_eq_guard_slice (z t : Fin 19) :
    b4Type22Block z t =
      ∑ R ∈ (Finset.univ : Finset (Fin 10)).filter
        (fun R => R.val ≤ z.val+t.val ∧ z.val+t.val+R.val ≤ 18),
        if type22Accept (z,t,R) then
          min z.val R.val+1-(R.val-t.val) else 0 := by
  unfold b4Type22Block
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro R _
  by_cases ha : type22Accept (z,t,R)
  · simp only [ha, ite_true, type22_accept_q_le z t R ha,
      type22_accept_budget z t R ha, and_self]
  · simp [ha]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_block_eq_guard_slice

theorem b4_type112_block_eq_guard_slice (z : Fin 38) (t : Fin 19) (u : Fin 38) :
    b4Type112Block z t u =
      ∑ Q ∈ (Finset.univ : Finset (Fin 19)).filter
        (fun Q => Q.val ≤ z.val+2*t.val+u.val ∧ z.val+2*t.val+u.val+Q.val ≤ 37),
        if B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val then
          b4Type112RowWeight (z,t,u,Q) else 0 := by
  unfold b4Type112Block
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases ha : B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val
  · simp only [ha, ite_true, type112_accept_q_le z t u Q ha,
      type112_accept_budget z t u Q ha, and_self]
  · simp [ha]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_block_eq_guard_slice

theorem b4_type22_block_zero_of_budget (z t : Fin 19)
    (hlarge : 19 ≤ z.val+t.val) : b4Type22Block z t = 0 := by
  unfold b4Type22Block
  apply Finset.sum_eq_zero
  intro R _
  have ha : ¬ type22Accept (z,t,R) := by
    intro h
    have hb := type22_accept_budget z t R h
    omega
  simp only [ha, ite_false]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_block_zero_of_budget

theorem b4_type112_block_zero_of_budget (z : Fin 38) (t : Fin 19) (u : Fin 38)
    (hlarge : 38 ≤ z.val+2*t.val+u.val) : b4Type112Block z t u = 0 := by
  unfold b4Type112Block
  apply Finset.sum_eq_zero
  intro Q _
  have ha : ¬ B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val := by
    intro h
    have hb := type112_accept_budget z t u Q h
    omega
  simp only [ha, ite_false]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_block_zero_of_budget

theorem b4_type22_finite_sum_eq_budget_slices :
    b4Type22FiniteSum = ∑ z : Fin 19,
      ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => z.val+t.val ≤ 18),
        b4Type22Block z t := by
  rw [b4_type22_finite_sum_eq_blocks]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : z.val+t.val ≤ 18
  · simp only [h, ite_true]
  · have hz := b4_type22_block_zero_of_budget z t (by omega)
    simp only [h, ite_false, hz]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_finite_sum_eq_budget_slices

theorem b4_type112_finite_sum_eq_budget_slices :
    b4Type112FiniteSum = ∑ z : Fin 38, ∑ t : Fin 19,
      ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter
        (fun u => z.val+2*t.val+u.val ≤ 37), b4Type112Block z t u := by
  rw [b4_type112_finite_sum_eq_blocks]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : z.val+2*t.val+u.val ≤ 37
  · simp only [h, ite_true]
  · have hz := b4_type112_block_zero_of_budget z t u (by omega)
    simp only [h, ite_false, hz]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_finite_sum_eq_budget_slices

theorem b4_type22_top_strip_zero (z : Fin 19) (hz : 0 < z.val) :
    b4Type22Block z 18 = 0 := by
  apply b4_type22_block_zero_of_budget
  change 19 ≤ z.val+18
  omega
#print axioms Paper7MomentCanonicalNumeric.b4_type22_top_strip_zero

theorem b4_type112_top_plane_zero (t : Fin 19) (u : Fin 38)
    (h : 0 < 2*t.val+u.val) : b4Type112Block 37 t u = 0 := by
  apply b4_type112_block_zero_of_budget
  change 38 ≤ 37+2*t.val+u.val
  omega
#print axioms Paper7MomentCanonicalNumeric.b4_type112_top_plane_zero

end Paper7MomentCanonicalNumeric
