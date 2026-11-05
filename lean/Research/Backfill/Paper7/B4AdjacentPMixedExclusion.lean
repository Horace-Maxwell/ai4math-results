import Research.Backfill.Paper7.B4AdjacentPMixedRoots
import Research.Backfill.Paper7.B4SinglePMixedPolynomial
import Research.Backfill.Paper7.ControlB4CertifiedReduction

/-! Source-only complete exclusion for adjacent two-site P support with
arbitrary nonzero Q. Actual graph isomorphisms supply the transport. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem adjacent_two_p_mixed_nonintegral (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : p 2 = 0) (hp3 : p 3 = 0)
    (hq : 0 < ∑ i, q i) : ¬ IsIntegralGraph (SG 4 p q) := by
  obtain ⟨t,ht0,ht1,hHt⟩ := adjacent_two_p_small_root p q hp0 hp1 hq
  have hFt : mixedPolynomial p q t = 0 := by
    rw [adjacent_p_mixed_factor p q hp2 hp3 t,hHt,mul_zero]
  exact mixed_small_root_nonintegral p q t ht0 ht1 hFt
#print axioms Paper7B4Analytic.adjacent_two_p_mixed_nonintegral

theorem adjacent_two_p_dihedral_mixed_nonintegral (p q : Fin 4 → ℕ)
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (hp0 : 0 < p (σ 0)) (hp1 : 0 < p (σ 1))
    (hp2 : p (σ 2) = 0) (hp3 : p (σ 3) = 0)
    (hq : 0 < ∑ i, q i) : ¬ IsIntegralGraph (SG 4 p q) := by
  intro hG
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 p q (p ∘ σ) (q ∘ σ)
    (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hsum : ∑ i, (q ∘ σ) i = ∑ i, q i :=
    (Paper7PruningCanonical.dihedral_bijective 4 (by decide) σ hσ).sum_comp q
  have hq' : 0 < ∑ i, (q ∘ σ) i := by rw [hsum]; exact hq
  exact adjacent_two_p_mixed_nonintegral (p ∘ σ) (q ∘ σ) hp0 hp1 hp2 hp3 hq' hI
#print axioms Paper7B4Analytic.adjacent_two_p_dihedral_mixed_nonintegral

theorem adjacent_two_p_sites_mixed_nonintegral (p q : Fin 4 → ℕ) (i : Fin 4)
    (hpi : 0 < p i) (hpi1 : 0 < p (i+1))
    (hp : ∀ j : Fin 4, j ≠ i → j ≠ i+1 → p j = 0)
    (hq : 0 < ∑ j, q j) : ¬ IsIntegralGraph (SG 4 p q) := by
  let σ : Fin 4 → Fin 4 := fun k => k+i
  have hσ : IsDihedral 4 σ := by
    refine ⟨i,Or.inl ?_⟩
    intro k
    fin_cases i <;> fin_cases k <;> decide
  have h0 : 0 < p (σ 0) := by simpa [σ] using hpi
  have h1 : 0 < p (σ 1) := by simpa [σ,add_comm] using hpi1
  have h2 : p (σ 2) = 0 := by
    apply hp <;> fin_cases i <;> decide
  have h3 : p (σ 3) = 0 := by
    apply hp <;> fin_cases i <;> decide
  exact adjacent_two_p_dihedral_mixed_nonintegral p q σ hσ h0 h1 h2 h3 hq
#print axioms Paper7B4Analytic.adjacent_two_p_sites_mixed_nonintegral

theorem original_adjacent_two_p_mixed_nonintegral (L : Fin 4 → List ℕ) (i : Fin 4)
    (hpi : 0 < Paper7Normalize.countP1 4 L i)
    (hpi1 : 0 < Paper7Normalize.countP1 4 L (i+1))
    (hp : ∀ j : Fin 4, j ≠ i → j ≠ i+1 → Paper7Normalize.countP1 4 L j = 0)
    (hq : 0 < ∑ j, Paper7Normalize.countP2 4 L j) :
    ¬ IsIntegralGraph (sunGraph 4 L) := by
  intro hG
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 4 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 4 L
  let q := Paper7Normalize.countP2 4 L
  let e : sunGraph 4 L ≃g SG 4 p q := Paper7Normalize.sunNormalizeIso 4 L (by omega) hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  exact adjacent_two_p_sites_mixed_nonintegral p q i hpi hpi1 hp hq hI
#print axioms Paper7B4Analytic.original_adjacent_two_p_mixed_nonintegral

end Paper7B4Analytic
