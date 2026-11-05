import Research.Backfill.Paper7.MomentB4FixedTypeHighSlices
import Research.Backfill.Paper7.MomentB4FixedTypeArithmeticSlices

/-! Source-only exact triangular budget decomposition. Off-diagonal rows
have multiplicity two and diagonal rows retain multiplicity one. Every
remaining summand still tests the complete original catalogue predicate. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge.Legacy Paper7MomentCertificate Paper7MomentReduction
open scoped BigOperators Classical

theorem pair_interval_weight_comm (z t R : ℕ) :
    min z R+1-(R-t) = min t R+1-(R-z) := by
  rcases le_total z R with hz | hz
  · rcases le_total t R with ht | ht
    · rw [min_eq_left hz,min_eq_left ht]
      omega
    · rw [min_eq_left hz,min_eq_right ht]
      omega
  · rcases le_total t R with ht | ht
    · rw [min_eq_right hz,min_eq_left ht]
      omega
    · rw [min_eq_right hz,min_eq_right ht]
      omega
#print axioms Paper7MomentCanonicalNumeric.pair_interval_weight_comm

theorem type22_accept_swap (z t : Fin 19) (R : Fin 10) :
    type22Accept (z,t,R) ↔ type22Accept (t,z,R) := by
  have he : type22Row (t,z,R) = type22Row (z,t,R) ∘ Fin.revPerm := by
    funext i
    fin_cases i <;> rfl
  change B4CatalogRowAccept (type22Row (z,t,R)) (2*R.val) ↔
    B4CatalogRowAccept (type22Row (t,z,R)) (2*R.val)
  rw [he]
  exact (b4CatalogRowAccept_comp_perm (type22Row (z,t,R)) (2*R.val) Fin.revPerm).symm
#print axioms Paper7MomentCanonicalNumeric.type22_accept_swap

theorem type112_accept_swap (z : Fin 38) (t : Fin 19) (u : Fin 38) (Q : Fin 19) :
    B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val ↔
      B4CatalogRowAccept (type112Row (u,t,z,Q)) Q.val := by
  have he : type112Row (u,t,z,Q) =
      type112Row (z,t,u,Q) ∘ Equiv.swap (0 : Fin 4) 2 := by
    funext i
    fin_cases i <;> simp [type112Row, Equiv.swap_apply_def]
  rw [he]
  exact (b4CatalogRowAccept_comp_perm (type112Row (z,t,u,Q)) Q.val
    (Equiv.swap (0 : Fin 4) 2)).symm
#print axioms Paper7MomentCanonicalNumeric.type112_accept_swap

theorem b4_type112_row_weight_swap (z : Fin 38) (t : Fin 19)
    (u : Fin 38) (Q : Fin 19) :
    b4Type112RowWeight (z,t,u,Q) = b4Type112RowWeight (u,t,z,Q) := by
  unfold b4Type112RowWeight
  apply Finset.sum_congr rfl
  intro k _
  change (if k.val ≤ t.val ∧ 2*k.val ≤ Q.val then
    min z.val (Q.val-2*k.val)+1-((Q.val-2*k.val)-u.val) else 0) =
    (if k.val ≤ t.val ∧ 2*k.val ≤ Q.val then
      min u.val (Q.val-2*k.val)+1-((Q.val-2*k.val)-z.val) else 0)
  rw [pair_interval_weight_comm z.val u.val (Q.val-2*k.val)]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_row_weight_swap

theorem b4_type22_block_swap (z t : Fin 19) :
    b4Type22Block z t = b4Type22Block t z := by
  unfold b4Type22Block
  apply Finset.sum_congr rfl
  intro R _
  rw [type22_accept_swap z t R,pair_interval_weight_comm z.val t.val R.val]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_block_swap

theorem b4_type112_block_swap (z : Fin 38) (t : Fin 19) (u : Fin 38) :
    b4Type112Block z t u = b4Type112Block u t z := by
  unfold b4Type112Block
  apply Finset.sum_congr rfl
  intro Q _
  rw [type112_accept_swap z t u Q,b4_type112_row_weight_swap z t u Q]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_block_swap

theorem symmetric_finite_sum_triangle {A : Type} [Fintype A] [LinearOrder A]
    (f : A → A → ℕ) (hsym : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      2*(∑ i, ∑ j ∈ (Finset.univ : Finset A).filter (fun j => i < j), f i j) := by
  have hpart (i j : A) : f i j =
      (if i = j then f i j else 0) +
        (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · rw [ite_eq_right (ne_of_lt h),ite_eq_left h,ite_eq_right (not_lt_of_ge h.le)]
      omega
    · subst j
      simp
    · rw [ite_eq_right (ne_of_gt h),ite_eq_right (not_lt_of_ge h.le),ite_eq_left h]
      omega
  have hdiag : (∑ i, ∑ j, if i = j then f i j else 0) = ∑ i, f i i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have hswap : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have hsum : (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j, if i = j then f i j else 0) +
        (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
    calc
      _ = ∑ i, ∑ j, ((if i = j then f i j else 0) +
          (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_congr rfl (fun j _ => hpart i j)
      _ = _ := by simp only [Finset.sum_add_distrib]
  rw [hsum,hdiag,hswap]
  simp only [Finset.sum_filter]
  omega
#print axioms Paper7MomentCanonicalNumeric.symmetric_finite_sum_triangle

theorem b4_type22_finite_sum_eq_triangular_budget :
    b4Type22FiniteSum =
      (∑ z ∈ (Finset.univ : Finset (Fin 19)).filter (fun z => 2*z.val ≤ 18),
        b4Type22Block z z) +
      2*(∑ z : Fin 19, ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter
        (fun t => z < t ∧ z.val+t.val ≤ 18), b4Type22Block z t) := by
  rw [b4_type22_finite_sum_eq_blocks,
    symmetric_finite_sum_triangle b4Type22Block b4_type22_block_swap]
  apply congrArg₂ (fun a b : ℕ => a+2*b)
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : 2*z.val ≤ 18
    · exact (ite_eq_left h).symm
    · have hz := b4_type22_block_zero_of_budget z z (by omega)
      rw [ite_eq_right h,hz]
  · simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro t _
    by_cases hlt : z < t
    · by_cases hb : z.val+t.val ≤ 18
      · rw [ite_eq_left hlt,ite_eq_left (And.intro hlt hb)]
      · have hz := b4_type22_block_zero_of_budget z t (by omega)
        have hn : ¬ (z < t ∧ z.val+t.val ≤ 18) := fun h => hb h.2
        rw [ite_eq_left hlt,ite_eq_right hn,hz]
    · have hn : ¬ (z < t ∧ z.val+t.val ≤ 18) := fun h => hlt h.1
      rw [ite_eq_right hlt,ite_eq_right hn]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_finite_sum_eq_triangular_budget

theorem b4_type112_middle_sum_eq_triangular_budget (t : Fin 19) :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
      (∑ z ∈ (Finset.univ : Finset (Fin 38)).filter
        (fun z => 2*z.val+2*t.val ≤ 37), b4Type112Block z t z) +
      2*(∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter
        (fun u => z < u ∧ z.val+2*t.val+u.val ≤ 37), b4Type112Block z t u) := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z t u)
    (fun z u => b4_type112_block_swap z t u)]
  apply congrArg₂ (fun a b : ℕ => a+2*b)
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : 2*z.val+2*t.val ≤ 37
    · exact (ite_eq_left h).symm
    · have hz := b4_type112_block_zero_of_budget z t z (by omega)
      rw [ite_eq_right h,hz]
  · simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro u _
    by_cases hlt : z < u
    · by_cases hb : z.val+2*t.val+u.val ≤ 37
      · rw [ite_eq_left hlt,ite_eq_left (And.intro hlt hb)]
      · have hz := b4_type112_block_zero_of_budget z t u (by omega)
        have hn : ¬ (z < u ∧ z.val+2*t.val+u.val ≤ 37) := fun h => hb h.2
        rw [ite_eq_left hlt,ite_eq_right hn,hz]
    · have hn : ¬ (z < u ∧ z.val+2*t.val+u.val ≤ 37) := fun h => hlt h.1
      rw [ite_eq_right hlt,ite_eq_right hn]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle_sum_eq_triangular_budget

theorem b4_type112_finite_sum_eq_triangular_budget :
    b4Type112FiniteSum =
      ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 17),
        ((∑ z ∈ (Finset.univ : Finset (Fin 38)).filter
          (fun z => 2*z.val+2*t.val ≤ 37), b4Type112Block z t z) +
        2*(∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter
          (fun u => z < u ∧ z.val+2*t.val+u.val ≤ 37), b4Type112Block z t u)) := by
  rw [b4_type112_finite_sum_eq_blocks,Finset.sum_comm]
  calc
    _ = ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 17),
        ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.val < 17
      · exact (ite_eq_left ht).symm
      · have hz (z u : Fin 38) : b4Type112Block z t u = 0 :=
          b4_type112_block_zero_of_middle_ge_seventeen z t u (by omega)
        rw [ite_eq_right ht]
        exact Finset.sum_eq_zero (fun z _ =>
          Finset.sum_eq_zero (fun u _ => hz z u))
    _ = _ := Finset.sum_congr rfl
      (fun t _ => b4_type112_middle_sum_eq_triangular_budget t)
#print axioms Paper7MomentCanonicalNumeric.b4_type112_finite_sum_eq_triangular_budget

def b4Type22TriangleArithmeticTotal : ℕ :=
  (∑ z ∈ (Finset.univ : Finset (Fin 19)).filter (fun z => 2*z.val ≤ 18),
    ∑ R ∈ b4Type22ArithmeticDomain z z,
      if type22Accept (z,z,R) then min z.val R.val+1-(R.val-z.val) else 0) +
  2*(∑ z : Fin 19, ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter
    (fun t => z < t ∧ z.val+t.val ≤ 18), ∑ R ∈ b4Type22ArithmeticDomain z t,
      if type22Accept (z,t,R) then min z.val R.val+1-(R.val-t.val) else 0)
#print axioms Paper7MomentCanonicalNumeric.b4Type22TriangleArithmeticTotal

def b4Type112TriangleArithmeticTotal : ℕ :=
  ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 17),
    ((∑ z ∈ (Finset.univ : Finset (Fin 38)).filter
      (fun z => 2*z.val+2*t.val ≤ 37), ∑ Q ∈ b4Type112ArithmeticDomain z t z,
        if B4CatalogRowAccept (type112Row (z,t,z,Q)) Q.val then
          b4Type112RowWeight (z,t,z,Q) else 0) +
    2*(∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter
      (fun u => z < u ∧ z.val+2*t.val+u.val ≤ 37),
        ∑ Q ∈ b4Type112ArithmeticDomain z t u,
          if B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val then
            b4Type112RowWeight (z,t,u,Q) else 0))
#print axioms Paper7MomentCanonicalNumeric.b4Type112TriangleArithmeticTotal

theorem b4_type22_finite_sum_eq_triangle_arithmetic :
    b4Type22FiniteSum = b4Type22TriangleArithmeticTotal := by
  rw [b4_type22_finite_sum_eq_triangular_budget]
  unfold b4Type22TriangleArithmeticTotal
  simp_rw [← b4_type22_block_eq_arithmetic_slice]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_finite_sum_eq_triangle_arithmetic

theorem b4_type112_finite_sum_eq_triangle_arithmetic :
    b4Type112FiniteSum = b4Type112TriangleArithmeticTotal := by
  rw [b4_type112_finite_sum_eq_triangular_budget]
  unfold b4Type112TriangleArithmeticTotal
  simp_rw [← b4_type112_block_eq_arithmetic_slice]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_finite_sum_eq_triangle_arithmetic

theorem b4_canonical_clauses_iff_triangle_arithmetic :
    ((canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641) ∧
      ((canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641) ↔
        3*b4Type22TriangleArithmeticTotal+2*b4Type112TriangleArithmeticTotal = 10584 := by
  rw [b4_canonical_clauses_iff_two_finite_sums,
    b4_type22_finite_sum_eq_triangle_arithmetic,b4_type112_finite_sum_eq_triangle_arithmetic]
#print axioms Paper7MomentCanonicalNumeric.b4_canonical_clauses_iff_triangle_arithmetic

end Paper7MomentCanonicalNumeric
