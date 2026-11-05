import Research.Backfill.Paper7.MomentB4Type112MiddleFiveBounds

/-! SOURCE ONLY. Complete original catalogue on Fin11 x Fin16 endpoints.
The four kernel certificates cover every member in every endpoint group. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

def B4Type112FiveSupport (z u : ℕ) (sm : ℤ × ℤ) : Prop :=
  (sm = (29,324) ∧ (z,u) ∈ ({(0,13),(1,13),(2,13)} : Finset (ℕ × ℕ))) ∨
  (sm = (33,336) ∧ (z,u) ∈
    ({(3,13),(4,13),(6,12),(8,11),(9,10)} : Finset (ℕ × ℕ))) ∨
  (sm = (34,384) ∧ (z,u) ∈
    ({(0,15),(1,15),(2,15),(3,15),(5,14),(6,14),(7,13)} : Finset (ℕ × ℕ))) ∨
  (sm = (38,396) ∧ (z,u) ∈ ({(3,15),(6,14),(8,13)} : Finset (ℕ × ℕ)))
#print axioms Paper7MomentCanonicalNumeric.B4Type112FiveSupport

theorem type112_five_catalog_certificate_zero_to_two :
    ∀ z : Fin 3, ∀ u : Fin 16, ∀ sm ∈ b4FeatureCatalog,
      (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 5 (u.val-z.val) sm) ↔
        B4Type112FiveSupport z.val u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112FiveSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_five_catalog_certificate_zero_to_two

theorem type112_five_catalog_certificate_three_to_five :
    ∀ z : Fin 3, ∀ u : Fin 16, ∀ sm ∈ b4FeatureCatalog,
      (z.val+3 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+3+u.val) 5 (u.val-(z.val+3)) sm) ↔
        B4Type112FiveSupport (z.val+3) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112FiveSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_five_catalog_certificate_three_to_five

theorem type112_five_catalog_certificate_six_to_eight :
    ∀ z : Fin 3, ∀ u : Fin 16, ∀ sm ∈ b4FeatureCatalog,
      (z.val+6 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+6+u.val) 5 (u.val-(z.val+6)) sm) ↔
        B4Type112FiveSupport (z.val+6) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112FiveSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_five_catalog_certificate_six_to_eight

theorem type112_five_catalog_certificate_nine_to_ten :
    ∀ z : Fin 2, ∀ u : Fin 16, ∀ sm ∈ b4FeatureCatalog,
      (z.val+9 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+9+u.val) 5 (u.val-(z.val+9)) sm) ↔
        B4Type112FiveSupport (z.val+9) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112FiveSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_five_catalog_certificate_nine_to_ten

theorem type112_five_small_catalog_certificate (z : Fin 11) (u : Fin 16)
    (sm : ℤ × ℤ) (hm : sm ∈ b4FeatureCatalog) :
    (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 5 (u.val-z.val) sm) ↔
      B4Type112FiveSupport z.val u.val sm := by
  by_cases hz3 : z.val < 3
  · let i : Fin 3 := ⟨z.val,hz3⟩
    exact type112_five_catalog_certificate_zero_to_two i u sm hm
  · by_cases hz6 : z.val < 6
    · let i : Fin 3 := ⟨z.val-3,by omega⟩
      have hi : i.val+3 = z.val := by dsimp [i]; omega
      simpa only [hi] using type112_five_catalog_certificate_three_to_five i u sm hm
    · by_cases hz9 : z.val < 9
      · let i : Fin 3 := ⟨z.val-6,by omega⟩
        have hi : i.val+6 = z.val := by dsimp [i]; omega
        simpa only [hi] using type112_five_catalog_certificate_six_to_eight i u sm hm
      · let i : Fin 2 := ⟨z.val-9,by have := z.isLt; omega⟩
        have hi : i.val+9 = z.val := by dsimp [i]; omega
        simpa only [hi] using type112_five_catalog_certificate_nine_to_ten i u sm hm
#print axioms Paper7MomentCanonicalNumeric.type112_five_small_catalog_certificate

theorem type112_five_recovered_support (z u : Fin 38) (sm : ℤ × ℤ)
    (hzu : z ≤ u) (hm : sm ∈ b4FeatureCatalog)
    (hg : b4Type112RecoveredGuard (z.val+u.val) 5 (u.val-z.val) sm) :
    B4Type112FiveSupport z.val u.val sm := by
  have hQ : b4Type112RecoveredQ (z.val+u.val) 5 (u.val-z.val) sm.2 < 19 := by
    have := hg.2.2.1
    omega
  let Q : Fin 19 := ⟨b4Type112RecoveredQ (z.val+u.val) 5 (u.val-z.val) sm.2,hQ⟩
  have ha := (type112_accept_iff_recovered_catalog z 5 u Q hzu).mpr
    ⟨sm,hm,hg,rfl⟩
  have hb := type112_five_ordered_endpoint_bounds z u Q hzu ha
  let z' : Fin 11 := ⟨z.val,by omega⟩
  let u' : Fin 16 := ⟨u.val,by omega⟩
  exact (type112_five_small_catalog_certificate z' u' sm hm).mp ⟨hzu,hg⟩
#print axioms Paper7MomentCanonicalNumeric.type112_five_recovered_support

end Paper7MomentCanonicalNumeric
