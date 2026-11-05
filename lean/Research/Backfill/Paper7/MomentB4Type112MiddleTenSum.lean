import Research.Backfill.Paper7.MomentB4Type112MiddleTenValues

/-! SOURCE ONLY. The original complete middle10 sum is assembled from
the diagonal and the strictly ordered pairs, with the exact multiplier2.
The proposed value205 is a conclusion, never a premise of the guards. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_middle10_ordered_zero_outside (z u : Fin 38) (hzu : z ≤ u)
    (hnot : (z,u) ∉ ({(0,4),(0,5),(0,6),(0,9),(1,4),(1,5),(1,6),(1,9),
      (2,3),(2,5),(2,8),(2,9),(3,4),(3,5),(4,4),(4,8)} :
        Finset (Fin 38 × Fin 38))) : b4Type112Block z 10 u = 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 10 u hzu]
  unfold b4Type112RecoveredBlock
  apply Finset.sum_eq_zero
  intro sm hm
  apply ite_eq_right
  intro hg
  have hs := type112_ten_recovered_support z u sm hzu hm hg
  let s : Finset (ℕ × ℕ) :=
    {(0,4),(0,5),(0,6),(0,9),(1,4),(1,5),(1,6),(1,9),
      (2,3),(2,5),(2,8),(2,9),(3,4),(3,5),(4,4),(4,8)}
  have hN : (z.val,u.val) ∈ s := by
    rcases hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact (show ({(0,4),(0,5),(1,4),(2,3)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
    · exact (show ({(0,5),(0,6),(1,5),(1,6),(2,5),(3,4),(3,5),(4,4)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,9),(1,9),(2,8)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
    · exact (show ({(0,9),(1,9),(2,9),(4,8)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
  apply hnot
  norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
    Fin.ext_iff] at hN ⊢
  exact hN
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_ordered_zero_outside

theorem b4_type112_middle10_diagonal_sum :
    (∑ z : Fin 38, b4Type112Block z 10 z) = 9 := by
  calc
    _ = b4Type112Block 4 10 4 := by
      apply Finset.sum_eq_single (4 : Fin 38)
      · intro z _ hne
        apply b4_type112_middle10_ordered_zero_outside z z le_rfl
        have hv : z.val ≠ 4 := by
          intro he
          apply hne
          exact Fin.ext he
        simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
          Fin.ext_iff]
        omega
      · simp
    _ = 9 := b4_type112_middle10_four_four
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_diagonal_sum

theorem b4_type112_middle10_strict_triangle_sum :
    (∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter (fun u => z < u),
      b4Type112Block z 10 u) = 98 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(0,4),(0,5),(0,6),(0,9),(1,4),(1,5),(1,6),(1,9),
      (2,3),(2,5),(2,8),(2,9),(3,4),(3,5),(4,8)}
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p : Fin 38 × Fin 38,
        if p.1 < p.2 then b4Type112Block p.1 10 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, if p.1 < p.2 then b4Type112Block p.1 10 p.2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      by_cases hlt : p.1 < p.2
      · rw [ite_eq_left hlt]
        apply b4_type112_middle10_ordered_zero_outside p.1 p.2 hlt.le
        intro ho
        apply hp
        have he : ({(0,4),(0,5),(0,6),(0,9),(1,4),(1,5),(1,6),(1,9),
            (2,3),(2,5),(2,8),(2,9),(3,4),(3,5),(4,4),(4,8)} :
              Finset (Fin 38 × Fin 38)) = insert (4,4) s := by decide +kernel
        have hin : p ∈ insert (4,4) s := by
          rw [← he]
          exact ho
        rcases Finset.mem_insert.mp hin with h44 | hs
        · have hbad : (4 : Fin 38) < 4 := by simpa only [h44] using hlt
          exact False.elim ((lt_irrefl _) hbad)
        · exact hs
      · exact ite_eq_right hlt
    _ = 98 := by
      norm_num [s,b4_type112_middle10_zero_four,b4_type112_middle10_zero_five,
        b4_type112_middle10_zero_six,b4_type112_middle10_zero_nine,
        b4_type112_middle10_one_four,b4_type112_middle10_one_five,
        b4_type112_middle10_one_six,b4_type112_middle10_one_nine,
        b4_type112_middle10_two_three,b4_type112_middle10_two_five,
        b4_type112_middle10_two_eight,b4_type112_middle10_two_nine,
        b4_type112_middle10_three_four,b4_type112_middle10_three_five,
        b4_type112_middle10_four_eight]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_strict_triangle_sum

theorem b4_type112_complete_middle10_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 10 u) = 205 := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z 10 u)
    (fun z u => b4_type112_block_swap z 10 u)]
  rw [b4_type112_middle10_diagonal_sum,b4_type112_middle10_strict_triangle_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle10_sum

theorem b4_type112_first_eleven_eq_first_ten_add_205 :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 11),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 10),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+205 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 11 then F t else 0) =
        (if t.val < 10 then F t else 0)+(if t = 10 then F t else 0) := by
    by_cases hlt : t.val < 10
    · have ht : t.val < 11 := by omega
      have hn : t ≠ 10 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 10
      · subst t
        norm_num
      · have hn : ¬ t.val < 11 := by
          have hv : t.val ≠ 10 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 11 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 10 then F t else 0)+(if t = 10 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 10 then F t else 0)+F 10 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 10 = 205 := b4_type112_complete_middle10_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_eleven_eq_first_ten_add_205

end Paper7MomentCanonicalNumeric
