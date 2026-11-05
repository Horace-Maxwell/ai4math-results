import Research.Backfill.Paper7.MomentB4Type112MiddleThreeValues

/-! SOURCE ONLY. Complete original t=3 layer. Proposed646 is proved
from complete support and exact original weights, never assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_middle3_ordered_zero_outside (z u : Fin 38) (hzu : z ≤ u)
    (hnot : (z,u) ∉ ({(0,3),(0,5),(1,5),(0,4),(1,4),(2,4),(3,4),(2,3),(3,3),
      (0,13),(1,13),(0,12),(1,12),(2,12),(0,14),(1,14),(2,14),(3,14),(4,14),
      (6,13),(0,15),(1,15),(5,14),(7,13),(8,12),(10,11),(1,16),(2,16),(3,16),
      (6,15),(8,14),(11,12),(4,16),(10,13)} : Finset (Fin 38 × Fin 38))) :
    b4Type112Block z 3 u = 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 3 u hzu]
  unfold b4Type112RecoveredBlock
  apply Finset.sum_eq_zero
  intro sm hm
  apply ite_eq_right
  intro hg
  have hs := type112_three_recovered_support z u sm hzu hm hg
  let s : Finset (ℕ × ℕ) :=
    {(0,3),(0,5),(1,5),(0,4),(1,4),(2,4),(3,4),(2,3),(3,3),
      (0,13),(1,13),(0,12),(1,12),(2,12),(0,14),(1,14),(2,14),(3,14),(4,14),
      (6,13),(0,15),(1,15),(5,14),(7,13),(8,12),(10,11),(1,16),(2,16),(3,16),
      (6,15),(8,14),(11,12),(4,16),(10,13)}
  have hN : (z.val,u.val) ∈ s := by
    rcases hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ |
      ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact (show ({(0,3)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,5),(1,5),(0,4),(1,4),(2,4),(3,4),(2,3),(3,3)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,13),(1,13),(0,12),(1,12),(2,12)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,14),(1,14)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(2,14),(3,14),(4,14),(6,13)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,15),(1,15),(4,14),(5,14),(7,13),(8,12),(10,11)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(1,16),(2,16),(3,16),(6,15),(8,14),(11,12)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(4,16),(10,13),(11,12)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
  apply hnot
  norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
    Fin.ext_iff] at hN ⊢
  exact hN
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_ordered_zero_outside

theorem b4_type112_middle3_diagonal_sum :
    (∑ z : Fin 38, b4Type112Block z 3 z) = 8 := by
  calc
    _ = b4Type112Block 3 3 3 := by
      apply Finset.sum_eq_single (3 : Fin 38)
      · intro z _ hne
        apply b4_type112_middle3_ordered_zero_outside z z le_rfl
        have hv : z.val ≠ 3 := by
          intro he
          apply hne
          exact Fin.ext he
        norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Fin.ext_iff]
        omega
      · simp
    _ = 8 := b4_type112_middle3_three_three
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_diagonal_sum

theorem b4_type112_middle3_strict_triangle_sum :
    (∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter (fun u => z < u),
      b4Type112Block z 3 u) = 319 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(0,3),(0,5),(1,5),(0,4),(1,4),(2,4),(3,4),(2,3),(3,3),
      (0,13),(1,13),(0,12),(1,12),(2,12),(0,14),(1,14),(2,14),(3,14),(4,14),
      (6,13),(0,15),(1,15),(5,14),(7,13),(8,12),(10,11),(1,16),(2,16),(3,16),
      (6,15),(8,14),(11,12),(4,16),(10,13)}
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p : Fin 38 × Fin 38,
        if p.1 < p.2 then b4Type112Block p.1 3 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, if p.1 < p.2 then b4Type112Block p.1 3 p.2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      by_cases hlt : p.1 < p.2
      · rw [ite_eq_left hlt]
        exact b4_type112_middle3_ordered_zero_outside p.1 p.2 hlt.le hp
      · exact ite_eq_right hlt
    _ = 319 := by
      norm_num [s,b4_type112_middle3_zero_three,b4_type112_middle3_zero_five,
        b4_type112_middle3_one_five,b4_type112_middle3_zero_four,
        b4_type112_middle3_one_four,b4_type112_middle3_two_four,
        b4_type112_middle3_three_four,b4_type112_middle3_two_three,
        b4_type112_middle3_three_three,b4_type112_middle3_zero_thirteen,
        b4_type112_middle3_one_thirteen,b4_type112_middle3_zero_twelve,
        b4_type112_middle3_one_twelve,b4_type112_middle3_two_twelve,
        b4_type112_middle3_zero_fourteen,b4_type112_middle3_one_fourteen,
        b4_type112_middle3_two_fourteen,b4_type112_middle3_three_fourteen,
        b4_type112_middle3_four_fourteen,b4_type112_middle3_six_thirteen,
        b4_type112_middle3_zero_fifteen,b4_type112_middle3_one_fifteen,
        b4_type112_middle3_five_fourteen,b4_type112_middle3_seven_thirteen,
        b4_type112_middle3_eight_twelve,b4_type112_middle3_ten_eleven,
        b4_type112_middle3_one_sixteen,b4_type112_middle3_two_sixteen,
        b4_type112_middle3_three_sixteen,b4_type112_middle3_six_fifteen,
        b4_type112_middle3_eight_fourteen,b4_type112_middle3_eleven_twelve,
        b4_type112_middle3_four_sixteen,b4_type112_middle3_ten_thirteen]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_strict_triangle_sum

theorem b4_type112_complete_middle3_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 3 u) = 646 := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z 3 u)
    (fun z u => b4_type112_block_swap z 3 u)]
  norm_num [b4_type112_middle3_diagonal_sum,b4_type112_middle3_strict_triangle_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle3_sum

theorem b4_type112_first_four_eq_first_three_add_646 :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 4),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 3),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+646 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 4 then F t else 0) =
        (if t.val < 3 then F t else 0)+(if t = 3 then F t else 0) := by
    by_cases hlt : t.val < 3
    · have ht : t.val < 4 := by omega
      have hn : t ≠ 3 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 3
      · subst t
        norm_num
      · have hn : ¬ t.val < 4 := by
          have hv : t.val ≠ 3 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 4 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 3 then F t else 0)+(if t = 3 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 3 then F t else 0)+F 3 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 3 = 646 := b4_type112_complete_middle3_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_four_eq_first_three_add_646

end Paper7MomentCanonicalNumeric
