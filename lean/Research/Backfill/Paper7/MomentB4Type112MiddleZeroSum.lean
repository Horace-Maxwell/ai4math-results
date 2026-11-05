import Research.Backfill.Paper7.MomentB4Type112MiddleZeroValues

/-! SOURCE ONLY. The entire original t=0 layer and first1 are conclusions.
No global total or subtraction of previously evaluated layers is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_middle0_ordered_zero_outside (z u : Fin 38) (hzu : z ≤ u)
    (hnot : (z,u) ∉ ({(1,6),(2,6),(3,6),(3,5),(4,5),(4,4),(0,7),(1,7),
      (1,13),(2,13),(3,13),(4,12),(0,14),(1,14),(4,13),(5,13),(5,12),(6,12),
      (7,12),(7,11),(8,11),(8,10),(9,10),(9,9),
      (0,15),(1,15),(2,15),(3,15),(4,14),(5,14),(6,14),(7,13),(8,13),(8,12),(9,12),(10,11),
      (4,15),(7,14),(10,12),(11,11),(0,17),(1,17),(2,17),(5,16),(8,15),(9,14),(12,12),
      (6,16),(11,13),(0,23),(1,23),(6,22),(9,21),(0,24),(6,23),(9,22),(1,24),(13,20)} :
        Finset (Fin 38 × Fin 38))) : b4Type112Block z 0 u = 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 0 u hzu]
  unfold b4Type112RecoveredBlock
  apply Finset.sum_eq_zero
  intro sm hm
  apply ite_eq_right
  intro hg
  have hs := type112_zero_recovered_support z u sm hzu hm hg
  let s : Finset (ℕ × ℕ) :=
    {(1,6),(2,6),(3,6),(3,5),(4,5),(4,4),(0,7),(1,7),
      (1,13),(2,13),(3,13),(4,12),(0,14),(1,14),(4,13),(5,13),(5,12),(6,12),
      (7,12),(7,11),(8,11),(8,10),(9,10),(9,9),
      (0,15),(1,15),(2,15),(3,15),(4,14),(5,14),(6,14),(7,13),(8,13),(8,12),(9,12),(10,11),
      (4,15),(7,14),(10,12),(11,11),(0,17),(1,17),(2,17),(5,16),(8,15),(9,14),(12,12),
      (6,16),(11,13),(0,23),(1,23),(6,22),(9,21),(0,24),(6,23),(9,22),(1,24),(13,20)}
  have hN : (z.val,u.val) ∈ s := by
    rcases hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ |
      ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact (show ({(1,6),(2,6),(3,6),(3,5),(4,5),(4,4)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,7),(1,7),(3,6),(4,5)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(1,13),(2,13),(3,13),(4,12)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,14),(1,14),(3,13),(4,13),(5,13),(5,12),(6,12),(7,12),
        (7,11),(8,11),(8,10),(9,10),(9,9)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,15),(1,15),(2,15),(3,15),(4,14),(5,14),(6,14),(7,13),
        (8,13),(8,12),(9,12),(10,11)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(2,15),(3,15),(4,15),(5,14),(6,14),(7,13),(8,13),(9,12),(10,11)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(3,15),(4,15),(6,14),(7,14),(8,13),(10,12),(11,11)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,17),(1,17),(2,17),(5,16),(8,15),(9,14),(12,12)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(2,17),(6,16),(8,15),(11,13),(12,12)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,23),(1,23),(6,22),(9,21)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,24),(6,23),(9,22)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,24),(1,24),(13,20)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
  apply hnot
  norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
    Fin.ext_iff] at hN ⊢
  exact hN
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_ordered_zero_outside

theorem b4_type112_middle0_diagonal_sum :
    (∑ z : Fin 38, b4Type112Block z 0 z) = 31 := by
  let s : Finset (Fin 38) := {4,9,11,12}
  calc
    _ = ∑ z ∈ s, b4Type112Block z 0 z := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro z _ hz
      apply b4_type112_middle0_ordered_zero_outside z z le_rfl
      norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
        Fin.ext_iff] at hz ⊢
      omega
    _ = 31 := by
      norm_num [s,b4_type112_middle0_four_four,b4_type112_middle0_nine_nine,
        b4_type112_middle0_eleven_eleven,b4_type112_middle0_twelve_twelve]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_diagonal_sum

theorem b4_type112_middle0_strict_triangle_sum :
    (∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter (fun u => z < u),
      b4Type112Block z 0 u) = 301 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(1,6),(2,6),(3,6),(3,5),(4,5),(4,4),(0,7),(1,7),
      (1,13),(2,13),(3,13),(4,12),(0,14),(1,14),(4,13),(5,13),(5,12),(6,12),
      (7,12),(7,11),(8,11),(8,10),(9,10),(9,9),
      (0,15),(1,15),(2,15),(3,15),(4,14),(5,14),(6,14),(7,13),(8,13),(8,12),(9,12),(10,11),
      (4,15),(7,14),(10,12),(11,11),(0,17),(1,17),(2,17),(5,16),(8,15),(9,14),(12,12),
      (6,16),(11,13),(0,23),(1,23),(6,22),(9,21),(0,24),(6,23),(9,22),(1,24),(13,20)}
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p : Fin 38 × Fin 38,
        if p.1 < p.2 then b4Type112Block p.1 0 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, if p.1 < p.2 then b4Type112Block p.1 0 p.2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      by_cases hlt : p.1 < p.2
      · rw [ite_eq_left hlt]
        exact b4_type112_middle0_ordered_zero_outside p.1 p.2 hlt.le hp
      · exact ite_eq_right hlt
    _ = 301 := by
      norm_num [s,b4_type112_middle0_one_six,b4_type112_middle0_two_six,
        b4_type112_middle0_three_six,b4_type112_middle0_three_five,
        b4_type112_middle0_four_five,b4_type112_middle0_four_four,
        b4_type112_middle0_zero_seven,b4_type112_middle0_one_seven,
        b4_type112_middle0_one_thirteen,b4_type112_middle0_two_thirteen,
        b4_type112_middle0_three_thirteen,b4_type112_middle0_four_twelve,
        b4_type112_middle0_zero_fourteen,b4_type112_middle0_one_fourteen,
        b4_type112_middle0_four_thirteen,b4_type112_middle0_five_thirteen,
        b4_type112_middle0_five_twelve,b4_type112_middle0_six_twelve,
        b4_type112_middle0_seven_twelve,b4_type112_middle0_seven_eleven,
        b4_type112_middle0_eight_eleven,b4_type112_middle0_eight_ten,
        b4_type112_middle0_nine_ten,b4_type112_middle0_nine_nine,
        b4_type112_middle0_zero_fifteen,b4_type112_middle0_one_fifteen,
        b4_type112_middle0_two_fifteen,b4_type112_middle0_three_fifteen,
        b4_type112_middle0_four_fourteen,b4_type112_middle0_five_fourteen,
        b4_type112_middle0_six_fourteen,b4_type112_middle0_seven_thirteen,
        b4_type112_middle0_eight_thirteen,b4_type112_middle0_eight_twelve,
        b4_type112_middle0_nine_twelve,b4_type112_middle0_ten_eleven,
        b4_type112_middle0_four_fifteen,b4_type112_middle0_seven_fourteen,
        b4_type112_middle0_ten_twelve,b4_type112_middle0_eleven_eleven,
        b4_type112_middle0_zero_seventeen,b4_type112_middle0_one_seventeen,
        b4_type112_middle0_two_seventeen,b4_type112_middle0_five_sixteen,
        b4_type112_middle0_eight_fifteen,b4_type112_middle0_nine_fourteen,
        b4_type112_middle0_twelve_twelve,b4_type112_middle0_six_sixteen,
        b4_type112_middle0_eleven_thirteen,b4_type112_middle0_zero_twentythree,
        b4_type112_middle0_one_twentythree,b4_type112_middle0_six_twentytwo,
        b4_type112_middle0_nine_twentyone,b4_type112_middle0_zero_twentyfour,
        b4_type112_middle0_six_twentythree,b4_type112_middle0_nine_twentytwo,
        b4_type112_middle0_one_twentyfour,b4_type112_middle0_thirteen_twenty]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_strict_triangle_sum

theorem b4_type112_complete_middle0_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 0 u) = 633 := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z 0 u)
    (fun z u => b4_type112_block_swap z 0 u)]
  norm_num [b4_type112_middle0_diagonal_sum,b4_type112_middle0_strict_triangle_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle0_sum

theorem b4_type112_first_one_sum :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 1),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) = 633 := by
  have hf : ((Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 1)) = {0} := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro ht
      apply Fin.ext
      change t.val = 0
      omega
    · intro ht
      subst t
      norm_num
  rw [hf,Finset.sum_singleton]
  exact b4_type112_complete_middle0_sum
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_one_sum

end Paper7MomentCanonicalNumeric
