import Research.Backfill.Paper7.MomentB4Type22SumDifference

/-! SOURCE ONLY. Complete strict-triangle sum transported along a proved
bijection. No numerical table, sample, unproved catalogue cover, or total
is supplied as a premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open scoped BigOperators Classical

def b4Type22SDBlock (s : B4Type22StrictSD) : ℕ :=
  ∑ R : Fin 10, if b4Type22SDAccept s.val.1.val s.val.2.val R.val then
    min ((s.val.1.val-s.val.2.val)/2) R.val+1-
      (R.val-(s.val.1.val+s.val.2.val)/2) else 0
#print axioms Paper7MomentCanonicalNumeric.b4Type22SDBlock

theorem type22_sd_block_eq_decoded (s : B4Type22StrictSD) :
    b4Type22Block (type22StrictSDToPair s).val.1 (type22StrictSDToPair s).val.2 =
      b4Type22SDBlock s := by
  unfold b4Type22Block b4Type22SDBlock
  apply Finset.sum_congr rfl
  intro R _
  rw [type22_sd_decoded_accept]
  rfl
#print axioms Paper7MomentCanonicalNumeric.type22_sd_block_eq_decoded

theorem b4_type22_strict_pair_sum :
    (∑ p : B4Type22StrictPair, b4Type22Block p.val.1 p.val.2) =
      ∑ z : Fin 19, ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter
        (fun t => z < t ∧ z.val+t.val ≤ 18), b4Type22Block z t := by
  calc
    _ = ∑ p ∈ (Finset.univ : Finset (Fin 19 × Fin 19)).filter
        (fun p => p.1 < p.2 ∧ p.1.val+p.2.val ≤ 18), b4Type22Block p.1 p.2 := by
      exact (Finset.sum_subtype _ (fun _ => by simp)
        (fun p : Fin 19 × Fin 19 => b4Type22Block p.1 p.2)).symm
    _ = _ := by simp only [Finset.sum_filter,Fintype.sum_prod_type]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strict_pair_sum

theorem b4_type22_strict_triangle_eq_SD_sum :
    (∑ z : Fin 19, ∑ t ∈ (Finset.univ : Finset (Fin 19)).filter
      (fun t => z < t ∧ z.val+t.val ≤ 18), b4Type22Block z t) =
        ∑ s : B4Type22StrictSD, b4Type22SDBlock s := by
  rw [← b4_type22_strict_pair_sum]
  calc
    _ = ∑ s : B4Type22StrictSD,
        b4Type22Block (type22StrictSDToPair s).val.1 (type22StrictSDToPair s).val.2 := by
      exact (type22StrictPairSDEquiv.symm.sum_comp
        (fun p => b4Type22Block p.val.1 p.val.2)).symm
    _ = _ := Finset.sum_congr rfl (fun s _ => type22_sd_block_eq_decoded s)
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strict_triangle_eq_SD_sum

theorem b4_type22_finite_sum_eq_diagonal_and_SD :
    b4Type22FiniteSum =
      (∑ z ∈ (Finset.univ : Finset (Fin 19)).filter (fun z => 2*z.val ≤ 18),
        b4Type22Block z z) + 2*(∑ s : B4Type22StrictSD, b4Type22SDBlock s) := by
  rw [b4_type22_finite_sum_eq_triangular_budget,b4_type22_strict_triangle_eq_SD_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_finite_sum_eq_diagonal_and_SD

theorem b4_type22_SD_sum_eq_strips :
    (∑ s : B4Type22StrictSD, b4Type22SDBlock s) =
      ∑ S : Fin 19, b4Type22SDStrip S := by
  let f : Fin 19 × Fin 19 → ℕ := fun s =>
    ∑ R : Fin 10, if b4Type22SDAccept s.1.val s.2.val R.val then
      min ((s.1.val-s.2.val)/2) R.val+1-(R.val-(s.1.val+s.2.val)/2) else 0
  have hs : (∑ s : B4Type22StrictSD, b4Type22SDBlock s) =
      ∑ p ∈ (Finset.univ : Finset (Fin 19 × Fin 19)).filter
        (fun p => 0 < p.2.val ∧ p.2.val ≤ p.1.val ∧ (p.1.val-p.2.val)%2 = 0),
          f p := by
    exact (Finset.sum_subtype _ (fun _ => by simp) f).symm
  rw [hs,Finset.sum_filter,Fintype.sum_prod_type]
  unfold b4Type22SDStrip
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro D _
  by_cases h : 0 < D.val ∧ D.val ≤ S.val ∧ (S.val-D.val)%2 = 0
  · simp only [h,ite_true,true_and]
    rfl
  · simp only [h,ite_false,false_and,Finset.sum_const_zero]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_SD_sum_eq_strips

end Paper7MomentCanonicalNumeric
