import Research.Backfill.Paper7.MomentB4Type112MiddleElevenSupport

/-! SOURCE ONLY. The complete t=11 layer with the original weight. The
nine sorted endpoint pairs represent sixteen ordered pairs. Every
off-diagonal pair is counted twice, with no full Type112 total assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_eleven_block_eq_small_catalog (z u : Fin 38)
    (hzu : z ≤ u) (s : Finset (ℤ × ℤ)) (hsub : s ⊆ b4FeatureCatalog)
    (hcover : ∀ sm ∈ b4FeatureCatalog,
      b4Type112RecoveredGuard (z.val+u.val) 11 (u.val-z.val) sm → sm ∈ s) :
    b4Type112Block z 11 u = ∑ sm ∈ s,
      if b4Type112RecoveredGuard (z.val+u.val) 11 (u.val-z.val) sm then
        b4Type112PlainWeight z.val 11 u.val
          (b4Type112RecoveredQ (z.val+u.val) 11 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 11 u hzu]
  unfold b4Type112RecoveredBlock
  symm
  apply Finset.sum_subset hsub
  intro sm hm hnot
  apply ite_eq_right
  exact fun hg => hnot (hcover sm hm hg)
#print axioms Paper7MomentCanonicalNumeric.type112_eleven_block_eq_small_catalog

theorem b4_type112_middle11_zero_zero : b4Type112Block 0 11 0 = 1 := by
  rw [type112_eleven_block_eq_small_catalog 0 0 le_rfl {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eleven_recovered_support 0 0 sm le_rfl hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle11_zero_zero

theorem b4_type112_middle11_zero_one : b4Type112Block 0 11 1 = 1 := by
  rw [type112_eleven_block_eq_small_catalog 0 1 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eleven_recovered_support 0 1 sm (by decide) hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle11_zero_one

theorem b4_type112_middle11_zero_six : b4Type112Block 0 11 6 = 3 := by
  rw [type112_eleven_block_eq_small_catalog 0 6 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eleven_recovered_support 0 6 sm (by decide) hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle11_zero_six

theorem b4_type112_middle11_one_six : b4Type112Block 1 11 6 = 4 := by
  rw [type112_eleven_block_eq_small_catalog 1 6 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eleven_recovered_support 1 6 sm (by decide) hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle11_one_six

theorem b4_type112_middle11_two_five : b4Type112Block 2 11 5 = 9 := by
  rw [type112_eleven_block_eq_small_catalog 2 5 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eleven_recovered_support 2 5 sm (by decide) hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle11_two_five

theorem b4_type112_middle11_two_six : b4Type112Block 2 11 6 = 11 := by
  rw [type112_eleven_block_eq_small_catalog 2 6 (by decide) {(34,384),(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eleven_recovered_support 2 6 sm (by decide) hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle11_two_six

theorem b4_type112_middle11_three_five : b4Type112Block 3 11 5 = 6 := by
  rw [type112_eleven_block_eq_small_catalog 3 5 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eleven_recovered_support 3 5 sm (by decide) hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle11_three_five

theorem b4_type112_middle11_four_four : b4Type112Block 4 11 4 = 9 := by
  rw [type112_eleven_block_eq_small_catalog 4 4 le_rfl {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eleven_recovered_support 4 4 sm le_rfl hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle11_four_four

theorem b4_type112_middle11_four_five : b4Type112Block 4 11 5 = 9 := by
  rw [type112_eleven_block_eq_small_catalog 4 5 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eleven_recovered_support 4 5 sm (by decide) hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle11_four_five

theorem b4_type112_middle11_zero_outside (z u : Fin 38)
    (hnot : (z,u) ∉ ({(0,0),(0,1),(1,0),(0,6),(6,0),(1,6),(6,1),
      (2,5),(5,2),(2,6),(6,2),(3,5),(5,3),(4,4),(4,5),(5,4)} :
        Finset (Fin 38 × Fin 38))) : b4Type112Block z 11 u = 0 := by
  have hordered (a b : Fin 38) (hab : a ≤ b)
      (hn : (a,b) ∉ ({(0,0),(0,1),(1,0),(0,6),(6,0),(1,6),(6,1),
        (2,5),(5,2),(2,6),(6,2),(3,5),(5,3),(4,4),(4,5),(5,4)} :
          Finset (Fin 38 × Fin 38))) : b4Type112Block a 11 b = 0 := by
    rw [type112_block_eq_recovered_catalog_sum a 11 b hab]
    unfold b4Type112RecoveredBlock
    apply Finset.sum_eq_zero
    intro sm hm
    apply ite_eq_right
    intro hg
    have hs := type112_eleven_recovered_support a b sm hab hm hg
    rcases hs with ⟨_,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ |
      ⟨_,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ | ⟨_,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ <;>
      simp at hn
  rcases le_total z u with hzu | huz
  · exact hordered z u hzu hnot
  · rw [b4_type112_block_swap]
    apply hordered u z huz
    intro hin
    apply hnot
    simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at hin ⊢
    rcases hin with ⟨hu, hz⟩ | ⟨hu, hz⟩ | ⟨hu, hz⟩ | ⟨hu, hz⟩ |
      ⟨hu, hz⟩ | ⟨hu, hz⟩ | ⟨hu, hz⟩ | ⟨hu, hz⟩ | ⟨hu, hz⟩ |
      ⟨hu, hz⟩ | ⟨hu, hz⟩ | ⟨hu, hz⟩ | ⟨hu, hz⟩ | ⟨hu, hz⟩ |
      ⟨hu, hz⟩ | ⟨hu, hz⟩ <;> simp [hu, hz]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle11_zero_outside

theorem b4_type112_complete_middle11_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 11 u) = 96 := by
  let s : Finset (Fin 38 × Fin 38) :=
    {(0,0),(0,1),(1,0),(0,6),(6,0),(1,6),(6,1),(2,5),(5,2),
      (2,6),(6,2),(3,5),(5,3),(4,4),(4,5),(5,4)}
  have h10 : b4Type112Block 1 11 0 = 1 := by
    rw [b4_type112_block_swap,b4_type112_middle11_zero_one]
  have h60 : b4Type112Block 6 11 0 = 3 := by
    rw [b4_type112_block_swap,b4_type112_middle11_zero_six]
  have h61 : b4Type112Block 6 11 1 = 4 := by
    rw [b4_type112_block_swap,b4_type112_middle11_one_six]
  have h52 : b4Type112Block 5 11 2 = 9 := by
    rw [b4_type112_block_swap,b4_type112_middle11_two_five]
  have h62 : b4Type112Block 6 11 2 = 11 := by
    rw [b4_type112_block_swap,b4_type112_middle11_two_six]
  have h53 : b4Type112Block 5 11 3 = 6 := by
    rw [b4_type112_block_swap,b4_type112_middle11_three_five]
  have h54 : b4Type112Block 5 11 4 = 9 := by
    rw [b4_type112_block_swap,b4_type112_middle11_four_five]
  calc
    _ = ∑ p : Fin 38 × Fin 38, b4Type112Block p.1 11 p.2 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, b4Type112Block p.1 11 p.2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      exact b4_type112_middle11_zero_outside p.1 p.2 hp
    _ = 96 := by
      norm_num [s,b4_type112_middle11_zero_zero,b4_type112_middle11_zero_one,
        b4_type112_middle11_zero_six,b4_type112_middle11_one_six,
        b4_type112_middle11_two_five,b4_type112_middle11_two_six,
        b4_type112_middle11_three_five,b4_type112_middle11_four_four,
        b4_type112_middle11_four_five,h10,h60,h61,h52,h62,h53,h54]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle11_sum

theorem b4_type112_first_twelve_eq_first_eleven_add_ninety_six :
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 12),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) =
    (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 11),
      ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+96 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 12 then F t else 0) =
        (if t.val < 11 then F t else 0)+(if t = 11 then F t else 0) := by
    by_cases hlt : t.val < 11
    · have ht : t.val < 12 := by omega
      have hn : t ≠ 11 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 11
      · subst t
        norm_num
      · have hn : ¬ t.val < 12 := by
          have hv : t.val ≠ 11 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 12 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 11 then F t else 0)+(if t = 11 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 11 then F t else 0)+F 11 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 11 = 96 := b4_type112_complete_middle11_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_first_twelve_eq_first_eleven_add_ninety_six

end Paper7MomentCanonicalNumeric
