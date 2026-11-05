import Research.Backfill.Paper7.MomentB4Type112MiddleTwoValues

/-! SOURCE ONLY. Complete original t=2 layer and first3=first2+943.
The total is a conclusion of full support and original weights. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_middle2_ordered_zero_outside (z u : Fin 38) (hzu : z ≤ u)
    (hnot : (z,u) ∉ ({(0,5),(0,6),(1,6),(1,5),(2,5),(3,5),(3,4),(4,4),
      (0,13),(1,13),(2,13),(3,13),(3,12),(4,12),(0,15),(1,15),(2,15),(2,14),
      (3,14),(4,14),(5,14),(7,13),(8,12),(9,12),(10,11),(3,15),(6,14),
      (8,13),(4,16),(7,15),(9,14),(10,13),(11,12),(5,16)} :
        Finset (Fin 38 × Fin 38))) : b4Type112Block z 2 u = 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 2 u hzu]
  unfold b4Type112RecoveredBlock
  apply Finset.sum_eq_zero
  intro sm hm
  apply ite_eq_right
  intro hg
  have hs := type112_two_recovered_support z u sm hzu hm hg
  let s : Finset (ℕ × ℕ) :=
    {(0,5),(0,6),(1,6),(1,5),(2,5),(3,5),(3,4),(4,4),
      (0,13),(1,13),(2,13),(3,13),(3,12),(4,12),(0,15),(1,15),(2,15),(2,14),
      (3,14),(4,14),(5,14),(7,13),(8,12),(9,12),(10,11),(3,15),(6,14),
      (8,13),(4,16),(7,15),(9,14),(10,13),(11,12),(5,16)}
  have hN : (z.val,u.val) ∈ s := by
    rcases hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ |
      ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact (show ({(0,5)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,6),(1,6),(1,5),(2,5),(3,5),(3,4),(4,4)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,13),(1,13),(2,13),(3,13),(3,12),(4,12)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,15),(1,15),(2,15),(2,14),(3,14)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,15),(1,15),(2,15),(4,14),(5,14),(7,13),(8,12),(9,12),(10,11)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,15),(1,15),(2,15),(3,15),(5,14),(6,14),(7,13),(8,13),(9,12),(10,11)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(4,16),(7,15),(9,14),(10,13),(11,12)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(5,16),(9,14)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
  apply hnot
  norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
    Fin.ext_iff] at hN ⊢
  exact hN
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_ordered_zero_outside

theorem b4_type112_middle2_diagonal_sum :
    (∑ z : Fin 38, b4Type112Block z 2 z) = 9 := by
  calc
    _ = b4Type112Block 4 2 4 := by
      apply Finset.sum_eq_single (4 : Fin 38)
      · intro z _ hne
        apply b4_type112_middle2_ordered_zero_outside z z le_rfl
        have hv : z.val ≠ 4 := by
          intro he
          apply hne
          exact Fin.ext he
        norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Fin.ext_iff]
        omega
      · simp
    _ = 9 := b4_type112_middle2_four_four
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_diagonal_sum

theorem b4_type112_middle2_strict_triangle_sum :
    (∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter (fun u => z < u),
      b4Type112Block z 2 u) = 467 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(0,5),(0,6),(1,6),(1,5),(2,5),(3,5),(3,4),(4,4),
      (0,13),(1,13),(2,13),(3,13),(3,12),(4,12),(0,15),(1,15),(2,15),(2,14),
      (3,14),(4,14),(5,14),(7,13),(8,12),(9,12),(10,11),(3,15),(6,14),
      (8,13),(4,16),(7,15),(9,14),(10,13),(11,12),(5,16)}
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p : Fin 38 × Fin 38,
        if p.1 < p.2 then b4Type112Block p.1 2 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, if p.1 < p.2 then b4Type112Block p.1 2 p.2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      by_cases hlt : p.1 < p.2
      · rw [ite_eq_left hlt]
        exact b4_type112_middle2_ordered_zero_outside p.1 p.2 hlt.le hp
      · exact ite_eq_right hlt
    _ = 467 := by
      norm_num [s,b4_type112_middle2_zero_five,b4_type112_middle2_zero_six,
        b4_type112_middle2_one_six,b4_type112_middle2_one_five,
        b4_type112_middle2_two_five,b4_type112_middle2_three_five,
        b4_type112_middle2_three_four,b4_type112_middle2_four_four,
        b4_type112_middle2_zero_thirteen,b4_type112_middle2_one_thirteen,
        b4_type112_middle2_two_thirteen,b4_type112_middle2_three_thirteen,
        b4_type112_middle2_three_twelve,b4_type112_middle2_four_twelve,
        b4_type112_middle2_zero_fifteen,b4_type112_middle2_one_fifteen,
        b4_type112_middle2_two_fifteen,b4_type112_middle2_two_fourteen,
        b4_type112_middle2_three_fourteen,b4_type112_middle2_four_fourteen,
        b4_type112_middle2_five_fourteen,b4_type112_middle2_seven_thirteen,
        b4_type112_middle2_eight_twelve,b4_type112_middle2_nine_twelve,
        b4_type112_middle2_ten_eleven,b4_type112_middle2_three_fifteen,
        b4_type112_middle2_six_fourteen,b4_type112_middle2_eight_thirteen,
        b4_type112_middle2_four_sixteen,b4_type112_middle2_seven_fifteen,
        b4_type112_middle2_nine_fourteen,b4_type112_middle2_ten_thirteen,
        b4_type112_middle2_eleven_twelve,b4_type112_middle2_five_sixteen]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_strict_triangle_sum

theorem b4_type112_complete_middle2_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 2 u) = 943 := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z 2 u)
    (fun z u => b4_type112_block_swap z 2 u)]
  norm_num [b4_type112_middle2_diagonal_sum,b4_type112_middle2_strict_triangle_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle2_sum

theorem b4_type112_first_three_eq_first_two_add_943 :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 3),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 2),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+943 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 3 then F t else 0) =
        (if t.val < 2 then F t else 0)+(if t = 2 then F t else 0) := by
    by_cases hlt : t.val < 2
    · have ht : t.val < 3 := by omega
      have hn : t ≠ 2 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 2
      · subst t
        norm_num
      · have hn : ¬ t.val < 3 := by
          have hv : t.val ≠ 2 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 3 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 2 then F t else 0)+(if t = 2 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 2 then F t else 0)+F 2 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 2 = 943 := b4_type112_complete_middle2_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_three_eq_first_two_add_943

end Paper7MomentCanonicalNumeric
