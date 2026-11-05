import Research.Backfill.Paper7.MomentB4Type112MiddleFourValues

/-! SOURCE ONLY. Entire original t=4 layer, including five nonzero
diagonal blocks and seven double-fibre blocks. The proposed583 is a
conclusion, not a hypothesis. No t5 numerical theorem is imported. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_middle4_ordered_zero_outside (z u : Fin 38) (hzu : z ≤ u)
    (hnot : (z,u) ∉ ({(0,0),(0,1),(0,3),(1,3),(2,3),(0,2),(1,2),(2,2),(1,1),
      (0,12),(0,14),(1,14),(2,14),(3,14),(4,13),(5,13),(6,13),(7,12),(9,11),
      (10,10),(0,16),(4,15),(5,15),(7,14),(9,13),(10,12),(11,11),(1,16),
      (2,23),(3,23),(3,26)} : Finset (Fin 38 × Fin 38))) :
    b4Type112Block z 4 u = 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 4 u hzu]
  unfold b4Type112RecoveredBlock
  apply Finset.sum_eq_zero
  intro sm hm
  apply ite_eq_right
  intro hg
  have hs := type112_four_recovered_support z u sm hzu hm hg
  let s : Finset (ℕ × ℕ) :=
    {(0,0),(0,1),(0,3),(1,3),(2,3),(0,2),(1,2),(2,2),(1,1),
      (0,12),(0,14),(1,14),(2,14),(3,14),(4,13),(5,13),(6,13),(7,12),(9,11),
      (10,10),(0,16),(4,15),(5,15),(7,14),(9,13),(10,12),(11,11),(1,16),
      (2,23),(3,23),(3,26)}
  have hN : (z.val,u.val) ∈ s := by
    rcases hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ |
      ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact (show ({(0,0),(0,1)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,3),(1,3),(2,3),(0,2),(1,2),(2,2),(1,1)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,12)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,14),(1,14),(2,14),(3,14),(4,13)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,14),(1,14),(2,14),(3,14),(5,13),(6,13),(7,12),(9,11),(10,10)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,16),(4,15),(5,15),(7,14),(9,13),(10,12),(11,11)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,16),(1,16),(5,15),(9,13)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(2,23),(3,23)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(3,26)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
  apply hnot
  norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
    Fin.ext_iff] at hN ⊢
  exact hN
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_ordered_zero_outside

theorem b4_type112_middle4_diagonal_sum :
    (∑ z : Fin 38, b4Type112Block z 4 z) = 25 := by
  let s : Finset (Fin 38) := {0,1,2,10,11}
  calc
    _ = ∑ z ∈ s, b4Type112Block z 4 z := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro z _ hz
      apply b4_type112_middle4_ordered_zero_outside z z le_rfl
      norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
        Fin.ext_iff] at hz ⊢
      omega
    _ = 25 := by
      norm_num [s,b4_type112_middle4_zero_zero,b4_type112_middle4_one_one,
        b4_type112_middle4_two_two,b4_type112_middle4_ten_ten,
        b4_type112_middle4_eleven_eleven]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_diagonal_sum

theorem b4_type112_middle4_strict_triangle_sum :
    (∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter (fun u => z < u),
      b4Type112Block z 4 u) = 279 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(0,0),(0,1),(0,3),(1,3),(2,3),(0,2),(1,2),(2,2),(1,1),
      (0,12),(0,14),(1,14),(2,14),(3,14),(4,13),(5,13),(6,13),(7,12),(9,11),
      (10,10),(0,16),(4,15),(5,15),(7,14),(9,13),(10,12),(11,11),(1,16),
      (2,23),(3,23),(3,26)}
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p : Fin 38 × Fin 38,
        if p.1 < p.2 then b4Type112Block p.1 4 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, if p.1 < p.2 then b4Type112Block p.1 4 p.2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      by_cases hlt : p.1 < p.2
      · rw [ite_eq_left hlt]
        exact b4_type112_middle4_ordered_zero_outside p.1 p.2 hlt.le hp
      · exact ite_eq_right hlt
    _ = 279 := by
      norm_num [s,b4_type112_middle4_zero_zero,b4_type112_middle4_zero_one,
        b4_type112_middle4_zero_three,b4_type112_middle4_one_three,
        b4_type112_middle4_two_three,b4_type112_middle4_zero_two,
        b4_type112_middle4_one_two,b4_type112_middle4_two_two,
        b4_type112_middle4_one_one,b4_type112_middle4_zero_twelve,
        b4_type112_middle4_zero_fourteen,b4_type112_middle4_one_fourteen,
        b4_type112_middle4_two_fourteen,b4_type112_middle4_three_fourteen,
        b4_type112_middle4_four_thirteen,b4_type112_middle4_five_thirteen,
        b4_type112_middle4_six_thirteen,b4_type112_middle4_seven_twelve,
        b4_type112_middle4_nine_eleven,b4_type112_middle4_ten_ten,
        b4_type112_middle4_zero_sixteen,b4_type112_middle4_four_fifteen,
        b4_type112_middle4_five_fifteen,b4_type112_middle4_seven_fourteen,
        b4_type112_middle4_nine_thirteen,b4_type112_middle4_ten_twelve,
        b4_type112_middle4_eleven_eleven,b4_type112_middle4_one_sixteen,
        b4_type112_middle4_two_twentythree,b4_type112_middle4_three_twentythree,
        b4_type112_middle4_three_twentysix]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_strict_triangle_sum

theorem b4_type112_complete_middle4_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 4 u) = 583 := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z 4 u)
    (fun z u => b4_type112_block_swap z 4 u)]
  norm_num [b4_type112_middle4_diagonal_sum,b4_type112_middle4_strict_triangle_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle4_sum

theorem b4_type112_first_five_eq_first_four_add_583 :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 5),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 4),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+583 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 5 then F t else 0) =
        (if t.val < 4 then F t else 0)+(if t = 4 then F t else 0) := by
    by_cases hlt : t.val < 4
    · have ht : t.val < 5 := by omega
      have hn : t ≠ 4 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 4
      · subst t
        norm_num
      · have hn : ¬ t.val < 5 := by
          have hv : t.val ≠ 4 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 5 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 4 then F t else 0)+(if t = 4 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 4 then F t else 0)+F 4 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 4 = 583 := b4_type112_complete_middle4_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_five_eq_first_four_add_583

end Paper7MomentCanonicalNumeric
