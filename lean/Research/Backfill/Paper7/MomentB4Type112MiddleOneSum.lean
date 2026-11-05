import Research.Backfill.Paper7.MomentB4Type112MiddleOneValues

/-! SOURCE ONLY mathematical correction: restore the omitted diagonal fibre.
The proposed983 and original first2=first1+983 are conclusions, not assumptions. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_middle1_ordered_zero_outside (z u : Fin 38) (hzu : z ≤ u)
    (hnot : (z,u) ∉ ({(0,6),(1,6),(2,6),(2,5),(3,4),(3,6),(3,5),(4,5),(4,4),
      (0,13),(1,13),(2,13),(3,13),(4,13),(4,12),(5,12),(6,12),(6,11),(7,11),(8,11),(8,10),
      (0,15),(1,15),(2,15),(3,15),(3,14),(4,14),(5,14),(6,14),(6,13),(7,13),(8,13),(9,12),(10,11),
      (4,15),(0,17),(1,17),(5,16),(7,15),(9,14),(2,17),(8,15),(12,12),
      (5,22),(6,22),(5,23),(6,23),(0,24),(9,22),(11,21),(9,9)} :
        Finset (Fin 38 × Fin 38))) : b4Type112Block z 1 u = 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 1 u hzu]
  unfold b4Type112RecoveredBlock
  apply Finset.sum_eq_zero
  intro sm hm
  apply ite_eq_right
  intro hg
  have hs := type112_one_recovered_support z u sm hzu hm hg
  let s : Finset (ℕ × ℕ) :=
    {(0,6),(1,6),(2,6),(2,5),(3,4),(3,6),(3,5),(4,5),(4,4),
      (0,13),(1,13),(2,13),(3,13),(4,13),(4,12),(5,12),(6,12),(6,11),(7,11),(8,11),(8,10),
      (0,15),(1,15),(2,15),(3,15),(3,14),(4,14),(5,14),(6,14),(6,13),(7,13),(8,13),(9,12),(10,11),
      (4,15),(0,17),(1,17),(5,16),(7,15),(9,14),(2,17),(8,15),(12,12),
      (5,22),(6,22),(5,23),(6,23),(0,24),(9,22),(11,21),(9,9)}
  have hN : (z.val,u.val) ∈ s := by
    rcases hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ |
      ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact (show ({(0,6),(1,6),(2,6),(2,5),(3,4)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(1,6),(2,6),(3,6),(3,5),(4,5),(4,4)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,13),(1,13)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(1,13),(2,13),(3,13),(4,13),(4,12),(5,12),(6,12),(6,11),(7,11),(8,11),(8,10),(9,9)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,15),(1,15),(2,15),(3,15),(3,14),(4,14),(5,14),(6,14),(6,13)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,15),(1,15),(2,15),(3,15),(5,14),(6,14),(7,13),(8,13),(9,12),(10,11)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(2,15),(3,15),(4,15),(6,14),(8,13),(9,12)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,17),(1,17),(5,16),(7,15),(9,14)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,17),(1,17),(2,17),(8,15),(12,12)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(5,22),(6,22)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(5,23),(6,23)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,24),(6,23),(9,22),(11,21)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
  apply hnot
  norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
    Fin.ext_iff] at hN ⊢
  exact hN
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_ordered_zero_outside

theorem b4_type112_middle1_diagonal_sum :
    (∑ z : Fin 38, b4Type112Block z 1 z) = 29 := by
  let s : Finset (Fin 38) := {4,9,12}
  calc
    _ = ∑ z ∈ s, b4Type112Block z 1 z := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro z _ hz
      apply b4_type112_middle1_ordered_zero_outside z z le_rfl
      norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
        Fin.ext_iff] at hz ⊢
      omega
    _ = 29 := by
      norm_num [s,b4_type112_middle1_four_four,b4_type112_middle1_nine_nine,
        b4_type112_middle1_twelve_twelve]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_diagonal_sum

theorem b4_type112_middle1_strict_triangle_sum :
    (∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter (fun u => z < u),
      b4Type112Block z 1 u) = 477 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(0,6),(1,6),(2,6),(2,5),(3,4),(3,6),(3,5),(4,5),(4,4),
      (0,13),(1,13),(2,13),(3,13),(4,13),(4,12),(5,12),(6,12),(6,11),(7,11),(8,11),(8,10),
      (0,15),(1,15),(2,15),(3,15),(3,14),(4,14),(5,14),(6,14),(6,13),(7,13),(8,13),(9,12),(10,11),
      (4,15),(0,17),(1,17),(5,16),(7,15),(9,14),(2,17),(8,15),(12,12),
      (5,22),(6,22),(5,23),(6,23),(0,24),(9,22),(11,21),(9,9)}
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p : Fin 38 × Fin 38,
        if p.1 < p.2 then b4Type112Block p.1 1 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, if p.1 < p.2 then b4Type112Block p.1 1 p.2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      by_cases hlt : p.1 < p.2
      · rw [ite_eq_left hlt]
        exact b4_type112_middle1_ordered_zero_outside p.1 p.2 hlt.le hp
      · exact ite_eq_right hlt
    _ = 477 := by
      norm_num [s,b4_type112_middle1_zero_six,b4_type112_middle1_one_six,
        b4_type112_middle1_two_six,b4_type112_middle1_two_five,
        b4_type112_middle1_three_four,b4_type112_middle1_three_six,
        b4_type112_middle1_three_five,b4_type112_middle1_four_five,
        b4_type112_middle1_four_four,b4_type112_middle1_zero_thirteen,
        b4_type112_middle1_one_thirteen,b4_type112_middle1_two_thirteen,
        b4_type112_middle1_three_thirteen,b4_type112_middle1_four_thirteen,
        b4_type112_middle1_four_twelve,b4_type112_middle1_five_twelve,
        b4_type112_middle1_six_twelve,b4_type112_middle1_six_eleven,
        b4_type112_middle1_seven_eleven,b4_type112_middle1_eight_eleven,
        b4_type112_middle1_eight_ten,b4_type112_middle1_zero_fifteen,
        b4_type112_middle1_one_fifteen,b4_type112_middle1_two_fifteen,
        b4_type112_middle1_three_fifteen,b4_type112_middle1_three_fourteen,
        b4_type112_middle1_four_fourteen,b4_type112_middle1_five_fourteen,
        b4_type112_middle1_six_fourteen,b4_type112_middle1_six_thirteen,
        b4_type112_middle1_seven_thirteen,b4_type112_middle1_eight_thirteen,
        b4_type112_middle1_nine_twelve,b4_type112_middle1_ten_eleven,
        b4_type112_middle1_four_fifteen,b4_type112_middle1_zero_seventeen,
        b4_type112_middle1_one_seventeen,b4_type112_middle1_five_sixteen,
        b4_type112_middle1_seven_fifteen,b4_type112_middle1_nine_fourteen,
        b4_type112_middle1_two_seventeen,b4_type112_middle1_eight_fifteen,
        b4_type112_middle1_twelve_twelve,b4_type112_middle1_five_twentytwo,
        b4_type112_middle1_six_twentytwo,b4_type112_middle1_five_twentythree,
        b4_type112_middle1_six_twentythree,b4_type112_middle1_zero_twentyfour,
        b4_type112_middle1_nine_twentytwo,b4_type112_middle1_eleven_twentyone,
        b4_type112_middle1_nine_nine]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_strict_triangle_sum

theorem b4_type112_complete_middle1_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 1 u) = 983 := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z 1 u)
    (fun z u => b4_type112_block_swap z 1 u)]
  norm_num [b4_type112_middle1_diagonal_sum,b4_type112_middle1_strict_triangle_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle1_sum

theorem b4_type112_first_two_eq_first_one_add_983 :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 2),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 1),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+983 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 2 then F t else 0) =
        (if t.val < 1 then F t else 0)+(if t = 1 then F t else 0) := by
    by_cases hlt : t.val < 1
    · have ht : t.val < 2 := by omega
      have hn : t ≠ 1 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 1
      · subst t
        norm_num
      · have hn : ¬ t.val < 2 := by
          have hv : t.val ≠ 1 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 2 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 1 then F t else 0)+(if t = 1 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 1 then F t else 0)+F 1 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 1 = 983 := b4_type112_complete_middle1_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_two_eq_first_one_add_983

end Paper7MomentCanonicalNumeric
