import Research.Backfill.Paper7.MomentB4Type112MiddleSevenValues

/-! SOURCE ONLY. Complete original t=7 sum, including the zero diagonal
and the actual symmetry multiplier. The proposed value 200 is proved
from complete support and original weights, never assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_middle7_ordered_zero_outside (z u : Fin 38) (hzu : z ≤ u)
    (hnot : (z,u) ∉ ({(0,11),(2,11),(3,11),(4,11),(5,10),(6,10),
      (2,13),(3,13),(4,13),(6,12),(8,11),(9,10)} :
        Finset (Fin 38 × Fin 38))) : b4Type112Block z 7 u = 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 7 u hzu]
  unfold b4Type112RecoveredBlock
  apply Finset.sum_eq_zero
  intro sm hm
  apply ite_eq_right
  intro hg
  have hs := type112_seven_recovered_support z u sm hzu hm hg
  let s : Finset (ℕ × ℕ) :=
    {(0,11),(2,11),(3,11),(4,11),(5,10),(6,10),
      (2,13),(3,13),(4,13),(6,12),(8,11),(9,10)}
  have hN : (z.val,u.val) ∈ s := by
    rcases hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact (show ({(0,11)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(2,11),(3,11),(4,11),(5,10),(6,10)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(2,13),(3,13)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
    · exact (show ({(4,13),(6,12),(8,11),(9,10)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
  apply hnot
  norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
    Fin.ext_iff] at hN ⊢
  exact hN
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_ordered_zero_outside

theorem b4_type112_middle7_diagonal_sum :
    (∑ z : Fin 38, b4Type112Block z 7 z) = 0 := by
  apply Finset.sum_eq_zero
  intro z _
  apply b4_type112_middle7_ordered_zero_outside z z le_rfl
  norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Fin.ext_iff]
  omega
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_diagonal_sum

theorem b4_type112_middle7_strict_triangle_sum :
    (∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter (fun u => z < u),
      b4Type112Block z 7 u) = 100 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(0,11),(2,11),(3,11),(4,11),(5,10),(6,10),
      (2,13),(3,13),(4,13),(6,12),(8,11),(9,10)}
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p : Fin 38 × Fin 38,
        if p.1 < p.2 then b4Type112Block p.1 7 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, if p.1 < p.2 then b4Type112Block p.1 7 p.2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      by_cases hlt : p.1 < p.2
      · rw [ite_eq_left hlt]
        exact b4_type112_middle7_ordered_zero_outside p.1 p.2 hlt.le hp
      · exact ite_eq_right hlt
    _ = 100 := by
      norm_num [s,b4_type112_middle7_zero_eleven,b4_type112_middle7_two_eleven,
        b4_type112_middle7_three_eleven,b4_type112_middle7_four_eleven,
        b4_type112_middle7_five_ten,b4_type112_middle7_six_ten,
        b4_type112_middle7_two_thirteen,b4_type112_middle7_three_thirteen,
        b4_type112_middle7_four_thirteen,b4_type112_middle7_six_twelve,
        b4_type112_middle7_eight_eleven,b4_type112_middle7_nine_ten]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_strict_triangle_sum

theorem b4_type112_complete_middle7_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 7 u) = 200 := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z 7 u)
    (fun z u => b4_type112_block_swap z 7 u)]
  rw [b4_type112_middle7_diagonal_sum,b4_type112_middle7_strict_triangle_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle7_sum

theorem b4_type112_first_eight_eq_first_seven_add_200 :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 8),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 7),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+200 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 8 then F t else 0) =
        (if t.val < 7 then F t else 0)+(if t = 7 then F t else 0) := by
    by_cases hlt : t.val < 7
    · have ht : t.val < 8 := by omega
      have hn : t ≠ 7 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 7
      · subst t
        norm_num
      · have hn : ¬ t.val < 8 := by
          have hv : t.val ≠ 7 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 8 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 7 then F t else 0)+(if t = 7 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 7 then F t else 0)+F 7 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 7 = 200 := b4_type112_complete_middle7_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_eight_eq_first_seven_add_200

end Paper7MomentCanonicalNumeric
