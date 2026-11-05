import Research.Backfill.Paper7.MomentB4Type112MiddleNineValues

/-! SOURCE ONLY. Complete original t=9 layer from the three diagonal
blocks and all strictly ordered pairs. The multiplier is the actual
endpoint-swap multiplier 2. The value 168 occurs only as a conclusion. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_middle9_ordered_zero_outside (z u : Fin 38) (hzu : z ≤ u)
    (hnot : (z,u) ∉ ({(0,0),(0,1),(0,2),(1,1),(0,8),(1,8),(2,8),(3,8),
      (4,7),(5,6),(6,6),(0,11),(1,11),(4,10),(6,9)} :
        Finset (Fin 38 × Fin 38))) : b4Type112Block z 9 u = 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 9 u hzu]
  unfold b4Type112RecoveredBlock
  apply Finset.sum_eq_zero
  intro sm hm
  apply ite_eq_right
  intro hg
  have hs := type112_nine_recovered_support z u sm hzu hm hg
  let s : Finset (ℕ × ℕ) :=
    {(0,0),(0,1),(0,2),(1,1),(0,8),(1,8),(2,8),(3,8),
      (4,7),(5,6),(6,6),(0,11),(1,11),(4,10),(6,9)}
  have hN : (z.val,u.val) ∈ s := by
    rcases hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
    · exact (show ({(0,0),(0,1),(0,2),(1,1)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
    · exact (show ({(0,8),(1,8),(2,8),(3,8),(4,7),(5,6),(6,6)} :
        Finset (ℕ × ℕ)) ⊆ s by decide +kernel) h
    · exact (show ({(0,11)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
    · exact (show ({(0,11),(1,11),(4,10),(6,9)} : Finset (ℕ × ℕ)) ⊆ s
        by decide +kernel) h
  apply hnot
  norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
    Fin.ext_iff] at hN ⊢
  exact hN
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_ordered_zero_outside

theorem b4_type112_middle9_diagonal_sum :
    (∑ z : Fin 38, b4Type112Block z 9 z) = 4 := by
  let s : Finset (Fin 38) := {0,1,6}
  calc
    _ = ∑ z ∈ s, b4Type112Block z 9 z := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro z _ hz
      apply b4_type112_middle9_ordered_zero_outside z z le_rfl
      norm_num only [s,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,
        Fin.ext_iff] at hz ⊢
      omega
    _ = 4 := by
      norm_num [s,b4_type112_middle9_zero_zero,b4_type112_middle9_one_one,
        b4_type112_middle9_six_six]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_diagonal_sum

theorem b4_type112_middle9_strict_triangle_sum :
    (∑ z : Fin 38, ∑ u ∈ (Finset.univ : Finset (Fin 38)).filter (fun u => z < u),
      b4Type112Block z 9 u) = 82 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(0,1),(0,2),(0,8),(1,8),(2,8),(3,8),(4,7),(5,6),
      (0,11),(1,11),(4,10),(6,9)}
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p : Fin 38 × Fin 38,
        if p.1 < p.2 then b4Type112Block p.1 9 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, if p.1 < p.2 then b4Type112Block p.1 9 p.2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      by_cases hlt : p.1 < p.2
      · rw [ite_eq_left hlt]
        apply b4_type112_middle9_ordered_zero_outside p.1 p.2 hlt.le
        intro ho
        apply hp
        have he : ({(0,0),(0,1),(0,2),(1,1),(0,8),(1,8),(2,8),(3,8),
            (4,7),(5,6),(6,6),(0,11),(1,11),(4,10),(6,9)} :
              Finset (Fin 38 × Fin 38)) = insert (0,0) (insert (1,1) (insert (6,6) s)) := by
          decide +kernel
        have hin : p ∈ insert (0,0) (insert (1,1) (insert (6,6) s)) := by
          rw [← he]
          exact ho
        simp only [Finset.mem_insert] at hin
        rcases hin with h00 | h11 | h66 | hs
        · have hbad : (0 : Fin 38) < 0 := by simpa only [h00] using hlt
          exact False.elim ((lt_irrefl _) hbad)
        · have hbad : (1 : Fin 38) < 1 := by simpa only [h11] using hlt
          exact False.elim ((lt_irrefl _) hbad)
        · have hbad : (6 : Fin 38) < 6 := by simpa only [h66] using hlt
          exact False.elim ((lt_irrefl _) hbad)
        · exact hs
      · exact ite_eq_right hlt
    _ = 82 := by
      norm_num [s,b4_type112_middle9_zero_one,b4_type112_middle9_zero_two,
        b4_type112_middle9_zero_eight,b4_type112_middle9_one_eight,
        b4_type112_middle9_two_eight,b4_type112_middle9_three_eight,
        b4_type112_middle9_four_seven,b4_type112_middle9_five_six,
        b4_type112_middle9_zero_eleven,b4_type112_middle9_one_eleven,
        b4_type112_middle9_four_ten,b4_type112_middle9_six_nine]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_strict_triangle_sum

theorem b4_type112_complete_middle9_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 9 u) = 168 := by
  rw [symmetric_finite_sum_triangle (fun z u => b4Type112Block z 9 u)
    (fun z u => b4_type112_block_swap z 9 u)]
  rw [b4_type112_middle9_diagonal_sum,b4_type112_middle9_strict_triangle_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle9_sum

theorem b4_type112_first_ten_eq_first_nine_add_168 :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 10),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 9),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+168 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 10 then F t else 0) =
        (if t.val < 9 then F t else 0)+(if t = 9 then F t else 0) := by
    by_cases hlt : t.val < 9
    · have ht : t.val < 10 := by omega
      have hn : t ≠ 9 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 9
      · subst t
        norm_num
      · have hn : ¬ t.val < 10 := by
          have hv : t.val ≠ 9 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 10 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 9 then F t else 0)+(if t = 9 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 9 then F t else 0)+F 9 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 9 = 168 := b4_type112_complete_middle9_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_ten_eq_first_nine_add_168

end Paper7MomentCanonicalNumeric
