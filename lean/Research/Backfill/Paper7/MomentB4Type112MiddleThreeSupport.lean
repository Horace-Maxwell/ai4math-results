import Research.Backfill.Paper7.MomentB4Type112MiddleThreeBounds

/-! SOURCE ONLY. Full Fin19 x Fin27 domain and all nineteen catalogue
members, including every high moment, in seven complete certificates. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

def B4Type112ThreeSupport (z u : ℕ) (sm : ℤ × ℤ) : Prop :=
  (sm = (13,84) ∧ (z,u) ∈ ({(0,3)} : Finset (ℕ × ℕ))) ∨
  (sm = (17,96) ∧ (z,u) ∈
    ({(0,5),(1,5),(0,4),(1,4),(2,4),(3,4),(2,3),(3,3)} : Finset (ℕ × ℕ))) ∨
  (sm = (24,264) ∧ (z,u) ∈
    ({(0,13),(1,13),(0,12),(1,12),(2,12)} : Finset (ℕ × ℕ))) ∨
  (sm = (25,312) ∧ (z,u) ∈ ({(0,14),(1,14)} : Finset (ℕ × ℕ))) ∨
  (sm = (29,324) ∧ (z,u) ∈ ({(2,14),(3,14),(4,14),(6,13)} : Finset (ℕ × ℕ))) ∨
  (sm = (33,336) ∧ (z,u) ∈
    ({(0,15),(1,15),(4,14),(5,14),(7,13),(8,12),(10,11)} : Finset (ℕ × ℕ))) ∨
  (sm = (34,384) ∧ (z,u) ∈
    ({(1,16),(2,16),(3,16),(6,15),(8,14),(11,12)} : Finset (ℕ × ℕ))) ∨
  (sm = (38,396) ∧ (z,u) ∈ ({(4,16),(10,13),(11,12)} : Finset (ℕ × ℕ)))
#print axioms Paper7MomentCanonicalNumeric.B4Type112ThreeSupport

theorem type112_three_catalog_certificate_zero_to_two :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 3 (u.val-z.val) sm) ↔
        B4Type112ThreeSupport z.val u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112ThreeSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Prod.mk.injEq] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_three_catalog_certificate_zero_to_two

theorem type112_three_catalog_certificate_three_to_five :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+3 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+3+u.val) 3 (u.val-(z.val+3)) sm) ↔
        B4Type112ThreeSupport (z.val+3) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112ThreeSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Prod.mk.injEq] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_three_catalog_certificate_three_to_five

theorem type112_three_catalog_certificate_six_to_eight :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+6 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+6+u.val) 3 (u.val-(z.val+6)) sm) ↔
        B4Type112ThreeSupport (z.val+6) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112ThreeSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Prod.mk.injEq] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_three_catalog_certificate_six_to_eight

theorem type112_three_catalog_certificate_nine_to_eleven :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+9 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+9+u.val) 3 (u.val-(z.val+9)) sm) ↔
        B4Type112ThreeSupport (z.val+9) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112ThreeSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Prod.mk.injEq] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_three_catalog_certificate_nine_to_eleven

theorem type112_three_catalog_certificate_twelve_to_fourteen :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+12 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+12+u.val) 3 (u.val-(z.val+12)) sm) ↔
        B4Type112ThreeSupport (z.val+12) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112ThreeSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Prod.mk.injEq] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_three_catalog_certificate_twelve_to_fourteen

theorem type112_three_catalog_certificate_fifteen_to_seventeen :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+15 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+15+u.val) 3 (u.val-(z.val+15)) sm) ↔
        B4Type112ThreeSupport (z.val+15) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112ThreeSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Prod.mk.injEq] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_three_catalog_certificate_fifteen_to_seventeen

theorem type112_three_catalog_certificate_eighteen :
    ∀ z : Fin 1, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+18 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+18+u.val) 3 (u.val-(z.val+18)) sm) ↔
        B4Type112ThreeSupport (z.val+18) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112ThreeSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Prod.mk.injEq] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_three_catalog_certificate_eighteen

theorem type112_three_small_catalog_certificate (z : Fin 19) (u : Fin 27)
    (sm : ℤ × ℤ) (hm : sm ∈ b4FeatureCatalog) :
    (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 3 (u.val-z.val) sm) ↔
      B4Type112ThreeSupport z.val u.val sm := by
  by_cases hz3 : z.val < 3
  · let i : Fin 3 := ⟨z.val,hz3⟩
    exact type112_three_catalog_certificate_zero_to_two i u sm hm
  · by_cases hz6 : z.val < 6
    · let i : Fin 3 := ⟨z.val-3,by omega⟩
      have hi : i.val+3 = z.val := by dsimp [i]; omega
      simpa only [hi] using type112_three_catalog_certificate_three_to_five i u sm hm
    · by_cases hz9 : z.val < 9
      · let i : Fin 3 := ⟨z.val-6,by omega⟩
        have hi : i.val+6 = z.val := by dsimp [i]; omega
        simpa only [hi] using type112_three_catalog_certificate_six_to_eight i u sm hm
      · by_cases hz12 : z.val < 12
        · let i : Fin 3 := ⟨z.val-9,by omega⟩
          have hi : i.val+9 = z.val := by dsimp [i]; omega
          simpa only [hi] using type112_three_catalog_certificate_nine_to_eleven i u sm hm
        · by_cases hz15 : z.val < 15
          · let i : Fin 3 := ⟨z.val-12,by omega⟩
            have hi : i.val+12 = z.val := by dsimp [i]; omega
            simpa only [hi] using type112_three_catalog_certificate_twelve_to_fourteen i u sm hm
          · by_cases hz18 : z.val < 18
            · let i : Fin 3 := ⟨z.val-15,by omega⟩
              have hi : i.val+15 = z.val := by dsimp [i]; omega
              simpa only [hi] using type112_three_catalog_certificate_fifteen_to_seventeen i u sm hm
            · let i : Fin 1 := ⟨z.val-18,by have := z.isLt; omega⟩
              have hi : i.val+18 = z.val := by dsimp [i]; omega
              simpa only [hi] using type112_three_catalog_certificate_eighteen i u sm hm
#print axioms Paper7MomentCanonicalNumeric.type112_three_small_catalog_certificate

theorem type112_three_recovered_support (z u : Fin 38) (sm : ℤ × ℤ)
    (hzu : z ≤ u) (hm : sm ∈ b4FeatureCatalog)
    (hg : b4Type112RecoveredGuard (z.val+u.val) 3 (u.val-z.val) sm) :
    B4Type112ThreeSupport z.val u.val sm := by
  have hQ : b4Type112RecoveredQ (z.val+u.val) 3 (u.val-z.val) sm.2 < 19 := by
    have := hg.2.2.1
    omega
  let Q : Fin 19 := ⟨b4Type112RecoveredQ (z.val+u.val) 3 (u.val-z.val) sm.2,hQ⟩
  have ha := (type112_accept_iff_recovered_catalog z 3 u Q hzu).mpr
    ⟨sm,hm,hg,rfl⟩
  have hb := type112_three_ordered_endpoint_bounds z u Q hzu ha
  let z' : Fin 19 := ⟨z.val,by omega⟩
  let u' : Fin 27 := ⟨u.val,by omega⟩
  exact (type112_three_small_catalog_certificate z' u' sm hm).mp ⟨hzu,hg⟩
#print axioms Paper7MomentCanonicalNumeric.type112_three_recovered_support

end Paper7MomentCanonicalNumeric
