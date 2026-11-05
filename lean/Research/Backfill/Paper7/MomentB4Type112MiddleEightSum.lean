import Research.Backfill.Paper7.MomentB4Type112MiddleEightValues

/-! SOURCE ONLY. Complete original t=8 layer: zero diagonal and all
strictly ordered blocks, with the proved endpoint-swap multiplier 2.
The value 144 is a conclusion and is never a guard assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_middle8_ordered_zero_outside (z u : Fin 38) (hzu : z ≤ u)
    (hnot : (z,u) ∉ ({(0,10),(1,10),(2,10),(3,10),(4,9),(5,9),
      (0,12),(1,12),(2,12),(3,12),(7,10)} :
        Finset (Fin 38 × Fin 38))) : b4Type112Block z 8 u = 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 8 u hzu]
  unfold b4Type112RecoveredBlock
  apply Finset.sum_eq_zero
  intro sm hm
  apply ite_eq_right
  intro hg
  have hs := type112_eight_recovered_support z u sm hzu hm hg
  let s : Finset (ℕ × ℕ) :=
    {(0,10),(1,10),(2,10),(3,10),(4,9),(5,9),
      (0,12),(1,12),(2,12),(3,12),(7,10)}
  have hN : (z.val,u.val) ∈ s := by
    rcases hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact (show ({(0,10),(1,10),(2,10),(3,10),(4,9),(5,9)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,12),(1,12),(2,12)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
    · exact (show ({(3,12),(7,10)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
  apply hnot
  norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
    Fin.ext_iff] at hN ⊢
  exact hN
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_ordered_zero_outside

theorem b4_type112_middle8_diagonal_sum :
    (∑ z : Fin 38, b4Type112Block z 8 z) = 0 := by
  apply Finset.sum_eq_zero
  intro z _
  apply b4_type112_middle8_ordered_zero_outside z z le_rfl
  norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Fin.ext_iff]
  omega
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_diagonal_sum

theorem b4_type112_middle8_strict_triangle_sum :
    (∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter (fun u => z < u),
      b4Type112Block z 8 u) = 72 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(0,10),(1,10),(2,10),(3,10),(4,9),(5,9),
      (0,12),(1,12),(2,12),(3,12),(7,10)}
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p : Fin 38 × Fin 38,
        if p.1 < p.2 then b4Type112Block p.1 8 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, if p.1 < p.2 then b4Type112Block p.1 8 p.2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      by_cases hlt : p.1 < p.2
      · rw [ite_eq_left hlt]
        exact b4_type112_middle8_ordered_zero_outside p.1 p.2 hlt.le hp
      · exact ite_eq_right hlt
    _ = 72 := by
      norm_num [s,b4_type112_middle8_zero_ten,b4_type112_middle8_one_ten,
        b4_type112_middle8_two_ten,b4_type112_middle8_three_ten,
        b4_type112_middle8_four_nine,b4_type112_middle8_five_nine,
        b4_type112_middle8_zero_twelve,b4_type112_middle8_one_twelve,
        b4_type112_middle8_two_twelve,b4_type112_middle8_three_twelve,
        b4_type112_middle8_seven_ten]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_strict_triangle_sum

theorem b4_type112_complete_middle8_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 8 u) = 144 := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z 8 u)
    (fun z u => b4_type112_block_swap z 8 u)]
  rw [b4_type112_middle8_diagonal_sum,b4_type112_middle8_strict_triangle_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle8_sum

theorem b4_type112_first_nine_eq_first_eight_add_144 :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 9),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 8),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+144 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 9 then F t else 0) =
        (if t.val < 8 then F t else 0)+(if t = 8 then F t else 0) := by
    by_cases hlt : t.val < 8
    · have ht : t.val < 9 := by omega
      have hn : t ≠ 8 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 8
      · subst t
        norm_num
      · have hn : ¬ t.val < 9 := by
          have hv : t.val ≠ 8 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 9 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 8 then F t else 0)+(if t = 8 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 8 then F t else 0)+F 8 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 8 = 144 := b4_type112_complete_middle8_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_nine_eq_first_eight_add_144

end Paper7MomentCanonicalNumeric
