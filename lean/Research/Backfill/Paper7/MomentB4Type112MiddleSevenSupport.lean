import Research.Backfill.Paper7.MomentB4Type112MiddleSevenBounds

/-! SOURCE ONLY. Complete original nineteen-member catalogue on the
analytically reduced Fin10 x Fin14 domain. Four certificate groups cover
z=0..2, 3..5, 6..8 and 9, without changing the recovered guard. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

def B4Type112SevenSupport (z u : ℕ) (sm : ℤ × ℤ) : Prop :=
  (sm = (29,324) ∧ (z,u) ∈ ({(0,11)} : Finset (ℕ × ℕ))) ∨
  (sm = (33,336) ∧ (z,u) ∈
    ({(2,11),(3,11),(4,11),(5,10),(6,10)} : Finset (ℕ × ℕ))) ∨
  (sm = (34,384) ∧ (z,u) ∈ ({(2,13),(3,13)} : Finset (ℕ × ℕ))) ∨
  (sm = (38,396) ∧ (z,u) ∈ ({(4,13),(6,12),(8,11),(9,10)} : Finset (ℕ × ℕ)))
#print axioms Paper7MomentCanonicalNumeric.B4Type112SevenSupport

theorem type112_seven_catalog_certificate_zero_to_two :
    ∀ z : Fin 3, ∀ u : Fin 14, ∀ sm ∈ b4FeatureCatalog,
      (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 7 (u.val-z.val) sm) ↔
        B4Type112SevenSupport z.val u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112SevenSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_seven_catalog_certificate_zero_to_two

theorem type112_seven_catalog_certificate_three_to_five :
    ∀ z : Fin 3, ∀ u : Fin 14, ∀ sm ∈ b4FeatureCatalog,
      (z.val+3 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+3+u.val) 7 (u.val-(z.val+3)) sm) ↔
        B4Type112SevenSupport (z.val+3) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112SevenSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_seven_catalog_certificate_three_to_five

theorem type112_seven_catalog_certificate_six_to_eight :
    ∀ z : Fin 3, ∀ u : Fin 14, ∀ sm ∈ b4FeatureCatalog,
      (z.val+6 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+6+u.val) 7 (u.val-(z.val+6)) sm) ↔
        B4Type112SevenSupport (z.val+6) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112SevenSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_seven_catalog_certificate_six_to_eight

theorem type112_seven_catalog_certificate_nine :
    ∀ z : Fin 1, ∀ u : Fin 14, ∀ sm ∈ b4FeatureCatalog,
      (z.val+9 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+9+u.val) 7 (u.val-(z.val+9)) sm) ↔
        B4Type112SevenSupport (z.val+9) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112SevenSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_seven_catalog_certificate_nine

theorem type112_seven_small_catalog_certificate (z : Fin 10) (u : Fin 14)
    (sm : ℤ × ℤ) (hm : sm ∈ b4FeatureCatalog) :
    (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 7 (u.val-z.val) sm) ↔
      B4Type112SevenSupport z.val u.val sm := by
  by_cases hz3 : z.val < 3
  · let i : Fin 3 := ⟨z.val,hz3⟩
    exact type112_seven_catalog_certificate_zero_to_two i u sm hm
  · by_cases hz6 : z.val < 6
    · let i : Fin 3 := ⟨z.val-3,by omega⟩
      have hi : i.val+3 = z.val := by dsimp [i]; omega
      simpa only [hi] using type112_seven_catalog_certificate_three_to_five i u sm hm
    · by_cases hz9 : z.val < 9
      · let i : Fin 3 := ⟨z.val-6,by omega⟩
        have hi : i.val+6 = z.val := by dsimp [i]; omega
        simpa only [hi] using type112_seven_catalog_certificate_six_to_eight i u sm hm
      · let i : Fin 1 := ⟨z.val-9,by have := z.isLt; omega⟩
        have hi : i.val+9 = z.val := by dsimp [i]; omega
        simpa only [hi] using type112_seven_catalog_certificate_nine i u sm hm
#print axioms Paper7MomentCanonicalNumeric.type112_seven_small_catalog_certificate

theorem type112_seven_recovered_support (z u : Fin 38) (sm : ℤ × ℤ)
    (hzu : z ≤ u) (hm : sm ∈ b4FeatureCatalog)
    (hg : b4Type112RecoveredGuard (z.val+u.val) 7 (u.val-z.val) sm) :
    B4Type112SevenSupport z.val u.val sm := by
  have hQ : b4Type112RecoveredQ (z.val+u.val) 7 (u.val-z.val) sm.2 < 19 := by
    have := hg.2.2.1
    omega
  let Q : Fin 19 := ⟨b4Type112RecoveredQ (z.val+u.val) 7 (u.val-z.val) sm.2,hQ⟩
  have ha := (type112_accept_iff_recovered_catalog z 7 u Q hzu).mpr
    ⟨sm,hm,hg,rfl⟩
  have hb := type112_seven_ordered_endpoint_bounds z u Q hzu ha
  let z' : Fin 10 := ⟨z.val,by omega⟩
  let u' : Fin 14 := ⟨u.val,by omega⟩
  exact (type112_seven_small_catalog_certificate z' u' sm hm).mp ⟨hzu,hg⟩
#print axioms Paper7MomentCanonicalNumeric.type112_seven_recovered_support

end Paper7MomentCanonicalNumeric
