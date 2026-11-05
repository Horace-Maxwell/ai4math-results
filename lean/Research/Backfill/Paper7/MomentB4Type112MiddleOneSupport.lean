import Research.Backfill.Paper7.MomentB4Type112MiddleOneBounds

/-! SOURCE ONLY mathematical correction after actual599 kernel counterexample.
Preserve Root03 Boolean normalization and the full original domain. The
existing (24,264) catalogue branch gains its omitted (9,9,Q=14) fibre. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators

def B4Type112OneSupport (z u : ℕ) (sm : ℤ × ℤ) : Prop :=
  (sm = (13,84) ∧ (z,u) ∈ ({(0,6),(1,6),(2,6),(2,5),(3,4)} : Finset (ℕ × ℕ))) ∨
  (sm = (17,96) ∧ (z,u) ∈ ({(1,6),(2,6),(3,6),(3,5),(4,5),(4,4)} : Finset (ℕ × ℕ))) ∨
  (sm = (20,252) ∧ (z,u) ∈ ({(0,13),(1,13)} : Finset (ℕ × ℕ))) ∨
  (sm = (24,264) ∧ (z,u) ∈
    ({(1,13),(2,13),(3,13),(4,13),(4,12),(5,12),(6,12),(6,11),(7,11),(8,11),(8,10),(9,9)} :
      Finset (ℕ × ℕ))) ∨
  (sm = (25,312) ∧ (z,u) ∈
    ({(0,15),(1,15),(2,15),(3,15),(3,14),(4,14),(5,14),(6,14),(6,13)} :
      Finset (ℕ × ℕ))) ∨
  (sm = (29,324) ∧ (z,u) ∈
    ({(0,15),(1,15),(2,15),(3,15),(5,14),(6,14),(7,13),(8,13),(9,12),(10,11)} :
      Finset (ℕ × ℕ))) ∨
  (sm = (33,336) ∧ (z,u) ∈
    ({(2,15),(3,15),(4,15),(6,14),(8,13),(9,12)} : Finset (ℕ × ℕ))) ∨
  (sm = (34,384) ∧ (z,u) ∈
    ({(0,17),(1,17),(5,16),(7,15),(9,14)} : Finset (ℕ × ℕ))) ∨
  (sm = (38,396) ∧ (z,u) ∈
    ({(0,17),(1,17),(2,17),(8,15),(12,12)} : Finset (ℕ × ℕ))) ∨
  (sm = (33,624) ∧ (z,u) ∈ ({(5,22),(6,22)} : Finset (ℕ × ℕ))) ∨
  (sm = (34,672) ∧ (z,u) ∈ ({(5,23),(6,23)} : Finset (ℕ × ℕ))) ∨
  (sm = (38,684) ∧ (z,u) ∈ ({(0,24),(6,23),(9,22),(11,21)} : Finset (ℕ × ℕ)))
#print axioms Paper7MomentCanonicalNumeric.B4Type112OneSupport

theorem type112_one_catalog_certificate_zero_to_two :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 1 (u.val-z.val) sm) ↔
        B4Type112OneSupport z.val u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112OneSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] <;>
    simp only [false_and,true_and,false_or,or_false] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_one_catalog_certificate_zero_to_two

theorem type112_one_catalog_certificate_three_to_five :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+3 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+3+u.val) 1 (u.val-(z.val+3)) sm) ↔
        B4Type112OneSupport (z.val+3) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112OneSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] <;>
    simp only [false_and,true_and,false_or,or_false] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_one_catalog_certificate_three_to_five

theorem type112_one_catalog_certificate_six_to_eight :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+6 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+6+u.val) 1 (u.val-(z.val+6)) sm) ↔
        B4Type112OneSupport (z.val+6) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112OneSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] <;>
    simp only [false_and,true_and,false_or,or_false] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_one_catalog_certificate_six_to_eight

theorem type112_one_catalog_certificate_nine_to_eleven :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+9 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+9+u.val) 1 (u.val-(z.val+9)) sm) ↔
        B4Type112OneSupport (z.val+9) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112OneSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] <;>
    simp only [false_and,true_and,false_or,or_false] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_one_catalog_certificate_nine_to_eleven

theorem type112_one_catalog_certificate_twelve_to_fourteen :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+12 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+12+u.val) 1 (u.val-(z.val+12)) sm) ↔
        B4Type112OneSupport (z.val+12) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112OneSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] <;>
    simp only [false_and,true_and,false_or,or_false] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_one_catalog_certificate_twelve_to_fourteen

theorem type112_one_catalog_certificate_fifteen_to_seventeen :
    ∀ z : Fin 3, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+15 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+15+u.val) 1 (u.val-(z.val+15)) sm) ↔
        B4Type112OneSupport (z.val+15) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112OneSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] <;>
    simp only [false_and,true_and,false_or,or_false] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_one_catalog_certificate_fifteen_to_seventeen

theorem type112_one_catalog_certificate_eighteen :
    ∀ z : Fin 1, ∀ u : Fin 27, ∀ sm ∈ b4FeatureCatalog,
      (z.val+18 ≤ u.val ∧
        b4Type112RecoveredGuard (z.val+18+u.val) 1 (u.val-(z.val+18)) sm) ↔
        B4Type112OneSupport (z.val+18) u.val sm := by
  intro z u ⟨S,M⟩ hm
  norm_num [b4FeatureCatalog] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm |
    hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    rcases hm with ⟨rfl,rfl⟩ <;> revert z u <;>
    simp only [B4Type112OneSupport,b4Type112RecoveredGuard,b4Type112RecoveredQ,
      b4Type112CatalogResidual,b4Type112DoubleBase] <;>
    norm_num only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] <;>
    simp only [false_and,true_and,false_or,or_false] <;> decide +kernel
#print axioms Paper7MomentCanonicalNumeric.type112_one_catalog_certificate_eighteen

theorem type112_one_small_catalog_certificate (z : Fin 19) (u : Fin 27)
    (sm : ℤ × ℤ) (hm : sm ∈ b4FeatureCatalog) :
    (z.val ≤ u.val ∧ b4Type112RecoveredGuard (z.val+u.val) 1 (u.val-z.val) sm) ↔
      B4Type112OneSupport z.val u.val sm := by
  by_cases hz3 : z.val < 3
  · let i : Fin 3 := ⟨z.val,hz3⟩
    exact type112_one_catalog_certificate_zero_to_two i u sm hm
  · by_cases hz6 : z.val < 6
    · let i : Fin 3 := ⟨z.val-3,by omega⟩
      have hi : i.val+3 = z.val := by dsimp [i]; omega
      simpa only [hi] using type112_one_catalog_certificate_three_to_five i u sm hm
    · by_cases hz9 : z.val < 9
      · let i : Fin 3 := ⟨z.val-6,by omega⟩
        have hi : i.val+6 = z.val := by dsimp [i]; omega
        simpa only [hi] using type112_one_catalog_certificate_six_to_eight i u sm hm
      · by_cases hz12 : z.val < 12
        · let i : Fin 3 := ⟨z.val-9,by omega⟩
          have hi : i.val+9 = z.val := by dsimp [i]; omega
          simpa only [hi] using type112_one_catalog_certificate_nine_to_eleven i u sm hm
        · by_cases hz15 : z.val < 15
          · let i : Fin 3 := ⟨z.val-12,by omega⟩
            have hi : i.val+12 = z.val := by dsimp [i]; omega
            simpa only [hi] using type112_one_catalog_certificate_twelve_to_fourteen i u sm hm
          · by_cases hz18 : z.val < 18
            · let i : Fin 3 := ⟨z.val-15,by omega⟩
              have hi : i.val+15 = z.val := by dsimp [i]; omega
              simpa only [hi] using type112_one_catalog_certificate_fifteen_to_seventeen i u sm hm
            · let i : Fin 1 := ⟨z.val-18,by have := z.isLt; omega⟩
              have hi : i.val+18 = z.val := by dsimp [i]; omega
              simpa only [hi] using type112_one_catalog_certificate_eighteen i u sm hm
#print axioms Paper7MomentCanonicalNumeric.type112_one_small_catalog_certificate

theorem type112_one_recovered_support (z u : Fin 38) (sm : ℤ × ℤ)
    (hzu : z ≤ u) (hm : sm ∈ b4FeatureCatalog)
    (hg : b4Type112RecoveredGuard (z.val+u.val) 1 (u.val-z.val) sm) :
    B4Type112OneSupport z.val u.val sm := by
  have hQ : b4Type112RecoveredQ (z.val+u.val) 1 (u.val-z.val) sm.2 < 19 := by
    have := hg.2.2.1
    omega
  let Q : Fin 19 := ⟨b4Type112RecoveredQ (z.val+u.val) 1 (u.val-z.val) sm.2,hQ⟩
  have ha := (type112_accept_iff_recovered_catalog z 1 u Q hzu).mpr
    ⟨sm,hm,hg,rfl⟩
  have hb := type112_one_ordered_endpoint_bounds z u Q hzu ha
  let z' : Fin 19 := ⟨z.val,by omega⟩
  let u' : Fin 27 := ⟨u.val,by omega⟩
  exact (type112_one_small_catalog_certificate z' u' sm hm).mp ⟨hzu,hg⟩
#print axioms Paper7MomentCanonicalNumeric.type112_one_recovered_support

end Paper7MomentCanonicalNumeric
