import Research.Backfill.Paper7.MomentB4Type112MiddleFiveValues

/-! SOURCE ONLY. Entire original t=5 layer and the original first6 to
first5 reduction. The proposed total 370 is a proof goal from complete
support and exact weights; it is not a hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_middle5_ordered_zero_outside (z u : Fin 38) (hzu : z ≤ u)
    (hnot : (z,u) ∉ ({(0,13),(1,13),(2,13),(3,13),(4,13),(6,12),(8,11),(9,10),
      (0,15),(1,15),(2,15),(3,15),(5,14),(6,14),(7,13),(8,13)} :
        Finset (Fin 38 × Fin 38))) : b4Type112Block z 5 u = 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 5 u hzu]
  unfold b4Type112RecoveredBlock
  apply Finset.sum_eq_zero
  intro sm hm
  apply ite_eq_right
  intro hg
  have hs := type112_five_recovered_support z u sm hzu hm hg
  let s : Finset (ℕ × ℕ) :=
    {(0,13),(1,13),(2,13),(3,13),(4,13),(6,12),(8,11),(9,10),
      (0,15),(1,15),(2,15),(3,15),(5,14),(6,14),(7,13),(8,13)}
  have hN : (z.val,u.val) ∈ s := by
    rcases hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact (show ({(0,13),(1,13),(2,13)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
    · exact (show ({(3,13),(4,13),(6,12),(8,11),(9,10)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,15),(1,15),(2,15),(3,15),(5,14),(6,14),(7,13)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(3,15),(6,14),(8,13)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
  apply hnot
  norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
    Fin.ext_iff] at hN ⊢
  exact hN
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_ordered_zero_outside

theorem b4_type112_middle5_diagonal_sum :
    (∑ z : Fin 38, b4Type112Block z 5 z) = 0 := by
  apply Finset.sum_eq_zero
  intro z _
  apply b4_type112_middle5_ordered_zero_outside z z le_rfl
  norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Fin.ext_iff]
  omega
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_diagonal_sum

theorem b4_type112_middle5_strict_triangle_sum :
    (∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter (fun u => z < u),
      b4Type112Block z 5 u) = 185 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(0,13),(1,13),(2,13),(3,13),(4,13),(6,12),(8,11),(9,10),
      (0,15),(1,15),(2,15),(3,15),(5,14),(6,14),(7,13),(8,13)}
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p : Fin 38 × Fin 38,
        if p.1 < p.2 then b4Type112Block p.1 5 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, if p.1 < p.2 then b4Type112Block p.1 5 p.2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      by_cases hlt : p.1 < p.2
      · rw [ite_eq_left hlt]
        exact b4_type112_middle5_ordered_zero_outside p.1 p.2 hlt.le hp
      · exact ite_eq_right hlt
    _ = 185 := by
      norm_num [s,b4_type112_middle5_zero_thirteen,b4_type112_middle5_one_thirteen,
        b4_type112_middle5_two_thirteen,b4_type112_middle5_three_thirteen,
        b4_type112_middle5_four_thirteen,b4_type112_middle5_six_twelve,
        b4_type112_middle5_eight_eleven,b4_type112_middle5_nine_ten,
        b4_type112_middle5_zero_fifteen,b4_type112_middle5_one_fifteen,
        b4_type112_middle5_two_fifteen,b4_type112_middle5_three_fifteen,
        b4_type112_middle5_five_fourteen,b4_type112_middle5_six_fourteen,
        b4_type112_middle5_seven_thirteen,b4_type112_middle5_eight_thirteen]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_strict_triangle_sum

theorem b4_type112_complete_middle5_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 5 u) = 370 := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z 5 u)
    (fun z u => b4_type112_block_swap z 5 u)]
  rw [b4_type112_middle5_diagonal_sum,b4_type112_middle5_strict_triangle_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle5_sum

theorem b4_type112_first_six_eq_first_five_add_370 :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 6),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 5),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+370 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 6 then F t else 0) =
        (if t.val < 5 then F t else 0)+(if t = 5 then F t else 0) := by
    by_cases hlt : t.val < 5
    · have ht : t.val < 6 := by omega
      have hn : t ≠ 5 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 5
      · subst t
        norm_num
      · have hn : ¬ t.val < 6 := by
          have hv : t.val ≠ 5 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 6 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 5 then F t else 0)+(if t = 5 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 5 then F t else 0)+F 5 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 5 = 370 := b4_type112_complete_middle5_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_six_eq_first_five_add_370

end Paper7MomentCanonicalNumeric
