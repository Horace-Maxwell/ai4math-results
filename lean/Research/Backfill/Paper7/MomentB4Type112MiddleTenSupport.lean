import Research.Backfill.Paper7.MomentB4Type112MiddleTenBounds

/-! SOURCE ONLY. Three separate complete finite certificates cover the
entire analytically reduced endpoint domain and the original catalogue.
No generated table, partial catalogue or full numerical total is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

def B4Type112TenSupport (z u : ℕ) (sm : ℤ × ℤ) : Prop :=
  (sm = (29,324) ∧ (z,u) ∈ ({(0,4),(0,5),(1,4),(2,3)} : Finset (ℕ × ℕ))) ∨
  (sm = (33,336) ∧ (z,u) ∈
    ({(0,5),(0,6),(1,5),(1,6),(2,5),(3,4),(3,5),(4,4)} : Finset (ℕ × ℕ))) ∨
  (sm = (34,384) ∧ (z,u) ∈ ({(0,9),(1,9),(2,8)} : Finset (ℕ × ℕ))) ∨
  (sm = (38,396) ∧ (z,u) ∈ ({(0,9),(1,9),(2,9),(4,8)} : Finset (ℕ × ℕ)))
#print axioms Paper7MomentCanonicalNumeric.B4Type112TenSupport

theorem type112_ten_catalog_certificate_zero_to_two :
    ∀ z : Fin 3, ∀ u : Fin 10, ∀ sm ∈ b4FeatureCatalog,
      (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 10 (u.val-z.val) sm) ↔
        B4Type112TenSupport z.val u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112TenSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_ten_catalog_certificate_zero_to_two

theorem type112_ten_catalog_certificate_three_to_four :
    ∀ z : Fin 2, ∀ u : Fin 10, ∀ sm ∈ b4FeatureCatalog,
      (z.val+3 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+3+u.val) 10 (u.val-(z.val+3)) sm) ↔
        B4Type112TenSupport (z.val+3) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112TenSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_ten_catalog_certificate_three_to_four

theorem type112_ten_catalog_certificate_five_to_six :
    ∀ z : Fin 2, ∀ u : Fin 10, ∀ sm ∈ b4FeatureCatalog,
      (z.val+5 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+5+u.val) 10 (u.val-(z.val+5)) sm) ↔
        B4Type112TenSupport (z.val+5) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112TenSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_ten_catalog_certificate_five_to_six

theorem type112_ten_small_catalog_certificate (z : Fin 7) (u : Fin 10)
    (sm : ℤ × ℤ) (hm : sm ∈ b4FeatureCatalog) :
    (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 10 (u.val-z.val) sm) ↔
      B4Type112TenSupport z.val u.val sm := by
  by_cases hz3 : z.val < 3
  · let i : Fin 3 := ⟨z.val,hz3⟩
    exact type112_ten_catalog_certificate_zero_to_two i u sm hm
  · by_cases hz5 : z.val < 5
    · let i : Fin 2 := ⟨z.val-3,by omega⟩
      have hi : i.val+3 = z.val := by dsimp [i]; omega
      simpa only [hi] using type112_ten_catalog_certificate_three_to_four i u sm hm
    · let i : Fin 2 := ⟨z.val-5,by have := z.isLt; omega⟩
      have hi : i.val+5 = z.val := by dsimp [i]; omega
      simpa only [hi] using type112_ten_catalog_certificate_five_to_six i u sm hm
#print axioms Paper7MomentCanonicalNumeric.type112_ten_small_catalog_certificate

theorem type112_ten_recovered_support (z u : Fin 38) (sm : ℤ × ℤ)
    (hzu : z ≤ u) (hm : sm ∈ b4FeatureCatalog)
    (hg : b4Type112RecoveredGuard (z.val+u.val) 10 (u.val-z.val) sm) :
    B4Type112TenSupport z.val u.val sm := by
  have hQ : b4Type112RecoveredQ (z.val+u.val) 10 (u.val-z.val) sm.2 < 19 := by
    have := hg.2.2.1
    omega
  let Q : Fin 19 := ⟨b4Type112RecoveredQ (z.val+u.val) 10 (u.val-z.val) sm.2,hQ⟩
  have ha := (type112_accept_iff_recovered_catalog z 10 u Q hzu).mpr
    ⟨sm,hm,hg,rfl⟩
  have hb := type112_ten_ordered_endpoint_bounds z u Q hzu ha
  let z' : Fin 7 := ⟨z.val,by omega⟩
  let u' : Fin 10 := ⟨u.val,by omega⟩
  exact (type112_ten_small_catalog_certificate z' u' sm hm).mp ⟨hzu,hg⟩
#print axioms Paper7MomentCanonicalNumeric.type112_ten_recovered_support

end Paper7MomentCanonicalNumeric
