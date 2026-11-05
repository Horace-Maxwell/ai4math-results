import Research.Backfill.Paper7.MomentB4Type112MiddleNineBounds

/-! SOURCE ONLY. Each certificate covers every original catalogue member.
The endpoint domain is partitioned into 36, 36 and 24 pairs; no executable
enumeration or generated table was used in authoring this candidate. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

def B4Type112NineSupport (z u : ℕ) (sm : ℤ × ℤ) : Prop :=
  (sm = (24,264) ∧ (z,u) ∈ ({(0,0),(0,1),(0,2),(1,1)} : Finset (ℕ × ℕ))) ∨
  (sm = (33,336) ∧ (z,u) ∈
    ({(0,8),(1,8),(2,8),(3,8),(4,7),(5,6),(6,6)} : Finset (ℕ × ℕ))) ∨
  (sm = (34,384) ∧ (z,u) ∈ ({(0,11)} : Finset (ℕ × ℕ))) ∨
  (sm = (38,396) ∧ (z,u) ∈ ({(0,11),(1,11),(4,10),(6,9)} : Finset (ℕ × ℕ)))
#print axioms Paper7MomentCanonicalNumeric.B4Type112NineSupport

theorem type112_nine_catalog_certificate_zero_to_two :
    ∀ z : Fin 3, ∀ u : Fin 12, ∀ sm ∈ b4FeatureCatalog,
      (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 9 (u.val-z.val) sm) ↔
        B4Type112NineSupport z.val u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112NineSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_nine_catalog_certificate_zero_to_two

theorem type112_nine_catalog_certificate_three_to_five :
    ∀ z : Fin 3, ∀ u : Fin 12, ∀ sm ∈ b4FeatureCatalog,
      (z.val+3 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+3+u.val) 9 (u.val-(z.val+3)) sm) ↔
        B4Type112NineSupport (z.val+3) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112NineSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_nine_catalog_certificate_three_to_five

theorem type112_nine_catalog_certificate_six_to_seven :
    ∀ z : Fin 2, ∀ u : Fin 12, ∀ sm ∈ b4FeatureCatalog,
      (z.val+6 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+6+u.val) 9 (u.val-(z.val+6)) sm) ↔
        B4Type112NineSupport (z.val+6) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112NineSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_nine_catalog_certificate_six_to_seven

theorem type112_nine_small_catalog_certificate (z : Fin 8) (u : Fin 12)
    (sm : ℤ × ℤ) (hm : sm ∈ b4FeatureCatalog) :
    (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 9 (u.val-z.val) sm) ↔
      B4Type112NineSupport z.val u.val sm := by
  by_cases hz3 : z.val < 3
  · let i : Fin 3 := ⟨z.val,hz3⟩
    exact type112_nine_catalog_certificate_zero_to_two i u sm hm
  · by_cases hz6 : z.val < 6
    · let i : Fin 3 := ⟨z.val-3,by omega⟩
      have hi : i.val+3 = z.val := by dsimp [i]; omega
      simpa only [hi] using type112_nine_catalog_certificate_three_to_five i u sm hm
    · let i : Fin 2 := ⟨z.val-6,by have := z.isLt; omega⟩
      have hi : i.val+6 = z.val := by dsimp [i]; omega
      simpa only [hi] using type112_nine_catalog_certificate_six_to_seven i u sm hm
#print axioms Paper7MomentCanonicalNumeric.type112_nine_small_catalog_certificate

theorem type112_nine_recovered_support (z u : Fin 38) (sm : ℤ × ℤ)
    (hzu : z ≤ u) (hm : sm ∈ b4FeatureCatalog)
    (hg : b4Type112RecoveredGuard (z.val+u.val) 9 (u.val-z.val) sm) :
    B4Type112NineSupport z.val u.val sm := by
  have hQ : b4Type112RecoveredQ (z.val+u.val) 9 (u.val-z.val) sm.2 < 19 := by
    have := hg.2.2.1
    omega
  let Q : Fin 19 := ⟨b4Type112RecoveredQ (z.val+u.val) 9 (u.val-z.val) sm.2,hQ⟩
  have ha := (type112_accept_iff_recovered_catalog z 9 u Q hzu).mpr
    ⟨sm,hm,hg,rfl⟩
  have hb := type112_nine_ordered_endpoint_bounds z u Q hzu ha
  let z' : Fin 8 := ⟨z.val,by omega⟩
  let u' : Fin 12 := ⟨u.val,by omega⟩
  exact (type112_nine_small_catalog_certificate z' u' sm hm).mp ⟨hzu,hg⟩
#print axioms Paper7MomentCanonicalNumeric.type112_nine_recovered_support

end Paper7MomentCanonicalNumeric
