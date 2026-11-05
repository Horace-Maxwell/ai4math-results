import Research.Backfill.Paper7.MomentB4Type112MiddleSixValues

/-! SOURCE ONLY. The original whole t=6 layer is assembled from the
single diagonal block and every strictly ordered block. The proposed
value 249 is a proof goal, without assuming any global numerical total. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_middle6_ordered_zero_outside (z u : Fin 38) (hzu : z ≤ u)
    (hnot : (z,u) ∉ ({(0,12),(1,12),(0,13),(3,12),(4,12),(6,11),(7,10),
      (9,9),(2,14),(3,14),(6,13),(4,14),(8,12)} :
        Finset (Fin 38 × Fin 38))) : b4Type112Block z 6 u = 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 6 u hzu]
  unfold b4Type112RecoveredBlock
  apply Finset.sum_eq_zero
  intro sm hm
  apply ite_eq_right
  intro hg
  have hs := type112_six_recovered_support z u sm hzu hm hg
  let s : Finset (ℕ × ℕ) :=
    {(0,12),(1,12),(0,13),(3,12),(4,12),(6,11),(7,10),
      (9,9),(2,14),(3,14),(6,13),(4,14),(8,12)}
  have hN : (z.val,u.val) ∈ s := by
    rcases hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact (show ({(0,12),(1,12)} : Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,13),(3,12),(4,12),(6,11),(7,10),(9,9)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(2,14),(3,14),(6,13)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
    · exact (show ({(4,14),(8,12)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
  apply hnot
  norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
    Fin.ext_iff] at hN ⊢
  exact hN
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_ordered_zero_outside

theorem b4_type112_middle6_diagonal_sum :
    (∑ z : Fin 38, b4Type112Block z 6 z) = 1 := by
  calc
    _ = b4Type112Block 9 6 9 := by
      apply Finset.sum_eq_single (9 : Fin 38)
      · intro z _ hne
        apply b4_type112_middle6_ordered_zero_outside z z le_rfl
        have hv : z.val ≠ 9 := by
          intro he
          apply hne
          exact Fin.ext he
        norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Fin.ext_iff]
        omega
      · simp
    _ = 1 := b4_type112_middle6_nine_nine
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_diagonal_sum

theorem b4_type112_middle6_strict_triangle_sum :
    (∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter (fun u => z < u),
      b4Type112Block z 6 u) = 124 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(0,12),(1,12),(0,13),(3,12),(4,12),(6,11),(7,10),
      (2,14),(3,14),(6,13),(4,14),(8,12)}
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p : Fin 38 × Fin 38,
        if p.1 < p.2 then b4Type112Block p.1 6 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, if p.1 < p.2 then b4Type112Block p.1 6 p.2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      by_cases hlt : p.1 < p.2
      · rw [ite_eq_left hlt]
        apply b4_type112_middle6_ordered_zero_outside p.1 p.2 hlt.le
        intro ho
        apply hp
        have he : ({(0,12),(1,12),(0,13),(3,12),(4,12),(6,11),(7,10),
            (9,9),(2,14),(3,14),(6,13),(4,14),(8,12)} :
              Finset (Fin 38 × Fin 38)) = insert (9,9) s := by decide +kernel
        have hin : p ∈ insert (9,9) s := by
          rw [← he]
          exact ho
        rcases Finset.mem_insert.mp hin with h99 | hs
        · have hbad : (9 : Fin 38) < 9 := by simpa only [h99] using hlt
          exact False.elim ((lt_irrefl _) hbad)
        · exact hs
      · exact ite_eq_right hlt
    _ = 124 := by
      norm_num [s,b4_type112_middle6_zero_twelve,b4_type112_middle6_one_twelve,
        b4_type112_middle6_zero_thirteen,b4_type112_middle6_three_twelve,
        b4_type112_middle6_four_twelve,b4_type112_middle6_six_eleven,
        b4_type112_middle6_seven_ten,b4_type112_middle6_two_fourteen,
        b4_type112_middle6_three_fourteen,b4_type112_middle6_six_thirteen,
        b4_type112_middle6_four_fourteen,b4_type112_middle6_eight_twelve]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_strict_triangle_sum

theorem b4_type112_complete_middle6_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 6 u) = 249 := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z 6 u)
    (fun z u => b4_type112_block_swap z 6 u)]
  rw [b4_type112_middle6_diagonal_sum,b4_type112_middle6_strict_triangle_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle6_sum

theorem b4_type112_first_seven_eq_first_six_add_249 :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 7),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 6),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+249 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 7 then F t else 0) =
        (if t.val < 6 then F t else 0)+(if t = 6 then F t else 0) := by
    by_cases hlt : t.val < 6
    · have ht : t.val < 7 := by omega
      have hn : t ≠ 6 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 6
      · subst t
        norm_num
      · have hn : ¬ t.val < 7 := by
          have hv : t.val ≠ 6 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 7 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 6 then F t else 0)+(if t = 6 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 6 then F t else 0)+F 6 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 6 = 249 := b4_type112_complete_middle6_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_seven_eq_first_six_add_249

end Paper7MomentCanonicalNumeric
