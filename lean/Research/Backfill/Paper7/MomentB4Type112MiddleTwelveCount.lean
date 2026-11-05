import Research.Backfill.Paper7.MomentB4Type112MiddleTwelveSupport

/-! SOURCE ONLY. Complete t=12 layer, evaluated after the proven Q
elimination. The four actual ordered endpoint pairs remain, so off-diagonal
multiplicity is two. The claimed layer value6 is a proposed conclusion,
not an assumption about the full5226 total. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_block_eq_small_catalog (z : Fin 38) (t : Fin 19) (u : Fin 38)
    (hzu : z ≤ u) (s : Finset (ℤ × ℤ)) (hsub : s ⊆ b4FeatureCatalog)
    (hcover : ∀ sm ∈ b4FeatureCatalog,
      b4Type112RecoveredGuard (z.val+u.val) t.val (u.val-z.val) sm → sm ∈ s) :
    b4Type112Block z t u = ∑ sm ∈ s,
      if b4Type112RecoveredGuard (z.val+u.val) t.val (u.val-z.val) sm then
        b4Type112PlainWeight z.val t.val u.val
          (b4Type112RecoveredQ (z.val+u.val) t.val (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z t u hzu]
  unfold b4Type112RecoveredBlock
  symm
  apply Finset.sum_subset hsub
  intro sm hm hnot
  apply ite_eq_right
  exact fun hg => hnot (hcover sm hm hg)
#print axioms Paper7MomentCanonicalNumeric.type112_block_eq_small_catalog

theorem b4_type112_middle12_zero_zero : b4Type112Block 0 12 0 = 2 := by
  rw [type112_block_eq_small_catalog 0 12 0 le_rfl {(34,384),(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_twelve_recovered_support 0 0 sm le_rfl hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle12_zero_zero

theorem b4_type112_middle12_zero_one : b4Type112Block 0 12 1 = 1 := by
  rw [type112_block_eq_small_catalog 0 12 1 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_twelve_recovered_support 0 1 sm (by decide) hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle12_zero_one

theorem b4_type112_middle12_one_one : b4Type112Block 1 12 1 = 2 := by
  rw [type112_block_eq_small_catalog 1 12 1 le_rfl {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_twelve_recovered_support 1 1 sm le_rfl hm hg
      simpa using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle12_one_one

theorem b4_type112_middle12_one_zero : b4Type112Block 1 12 0 = 1 := by
  rw [b4_type112_block_swap,b4_type112_middle12_zero_one]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle12_one_zero

theorem b4_type112_middle12_zero_outside (z u : Fin 38)
    (hnot : (z,u) ∉ ({(0,0),(0,1),(1,0),(1,1)} : Finset (Fin 38 × Fin 38))) :
    b4Type112Block z 12 u = 0 := by
  have hordered (a b : Fin 38) (hab : a ≤ b)
      (hn : (a,b) ∉ ({(0,0),(0,1),(1,0),(1,1)} : Finset (Fin 38 × Fin 38))) :
      b4Type112Block a 12 b = 0 := by
    rw [type112_block_eq_recovered_catalog_sum a 12 b hab]
    unfold b4Type112RecoveredBlock
    apply Finset.sum_eq_zero
    intro sm hm
    apply ite_eq_right
    intro hg
    have hs := type112_twelve_recovered_support a b sm hab hm hg
    rcases hs with ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ <;>
      simp at hn
  rcases le_total z u with hzu | huz
  · exact hordered z u hzu hnot
  · rw [b4_type112_block_swap]
    apply hordered u z huz
    intro hin
    apply hnot
    simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at hin ⊢
    rcases hin with ⟨hu,hz⟩ | ⟨hu,hz⟩ | ⟨hu,hz⟩ | ⟨hu,hz⟩ <;>
      simp [hu,hz]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle12_zero_outside

theorem b4_type112_complete_middle12_sum :
    (∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z 12 u) = 6 := by
  let s : Finset (Fin 38 × Fin 38) := {(0,0),(0,1),(1,0),(1,1)}
  calc
    _ = ∑ p : Fin 38 × Fin 38, b4Type112Block p.1 12 p.2 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ s, b4Type112Block p.1 12 p.2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _ hp
      exact b4_type112_middle12_zero_outside p.1 p.2 hp
    _ = 6 := by
      norm_num [s,b4_type112_middle12_zero_zero,b4_type112_middle12_zero_one,
        b4_type112_middle12_one_zero,b4_type112_middle12_one_one]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_complete_middle12_sum

theorem b4_type112_finite_sum_eq_first_twelve_add_six :
    b4Type112FiniteSum =
      (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 12),
        ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u)+6 := by
  let F : Fin 19 → ℕ := fun t => ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u
  have hpart (t : Fin 19) :
      (if t.val < 13 then F t else 0) =
        (if t.val < 12 then F t else 0)+(if t = 12 then F t else 0) := by
    by_cases hlt : t.val < 12
    · have ht : t.val < 13 := by omega
      have hn : t ≠ 12 := by intro h; subst t; norm_num at hlt
      simp only [ite_eq_left ht,ite_eq_left hlt,ite_eq_right hn,Nat.add_zero]
    · by_cases ht : t = 12
      · subst t
        norm_num
      · have hn : ¬ t.val < 13 := by
          have hv : t.val ≠ 12 := by
            intro h
            apply ht
            exact Fin.ext h
          omega
        simp only [ite_eq_right hn,ite_eq_right hlt,ite_eq_right ht,Nat.zero_add]
  rw [b4_type112_finite_sum_eq_thirteen_middle_slices,Finset.sum_filter]
  change (∑ t : Fin 19, if t.val < 13 then F t else 0) = _
  calc
    _ = ∑ t : Fin 19,
        ((if t.val < 12 then F t else 0)+(if t = 12 then F t else 0)) :=
      Finset.sum_congr rfl (fun t _ => hpart t)
    _ = (∑ t : Fin 19, if t.val < 12 then F t else 0)+F 12 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = _ := by
      have hF : F 12 = 6 := b4_type112_complete_middle12_sum
      rw [hF,Finset.sum_filter]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_finite_sum_eq_first_twelve_add_six

theorem b4_type112_5226_iff_first_twelve_5220 :
    b4Type112FiniteSum = 5226 ↔
      (∑ t ∈ (Finset.univ : Finset (Fin 19)).filter (fun t => t.val < 12),
        ∑ z : Fin 38, ∑ u : Fin 38, b4Type112Block z t u) = 5220 := by
  rw [b4_type112_finite_sum_eq_first_twelve_add_six]
  omega
#print axioms Paper7MomentCanonicalNumeric.b4_type112_5226_iff_first_twelve_5220

end Paper7MomentCanonicalNumeric
