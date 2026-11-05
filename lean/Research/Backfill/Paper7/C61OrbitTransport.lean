import Research.Backfill.Paper7.C61OrbitHelpers
import Research.Backfill.Paper7.HexagonSpectrum
import Research.Backfill.Paper7.GraphIsoIntegral
import Research.Backfill.Paper7.DihedralOrbitBasics

/-! Source-only continuation. C61OrbitHelpers is an explicitly pending old
candidate. The arbitrary-parameter classification is not asserted here. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Classification
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem c61_integral : IsIntegralGraph (SG 6 C61P (fun _ => 0)) := by
  have h := Paper7Hexagon.hexagon_six_integral
  rw [Paper7Hexagon.hexagon_six_eq, Paper7C61Orbit.c61_parameters] at h
  exact h
#print axioms Paper7C61Classification.c61_integral

theorem rotations_integral (p q : Fin 6 → ℕ)
    (hq : q = (fun _ => 0)) (hp : p ∈ C61Rotations) :
    IsIntegralGraph (SG 6 p q) := by
  obtain ⟨σ, hσ, hpσ⟩ := (Paper7C61Orbit.dihedral_orbit_iff p).mpr hp
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 6 C61P (fun _ => 0) p q
    (by decide) σ hσ hpσ hq
  exact Paper7Normalize.graphIso_integral _ _ e c61_integral
#print axioms Paper7C61Classification.rotations_integral

theorem rotations_comp_iff (p : Fin 6 → ℕ) (σ : Fin 6 → Fin 6)
    (hσ : IsDihedral 6 σ) : p ∘ σ ∈ C61Rotations ↔ p ∈ C61Rotations := by
  constructor
  · intro hp
    obtain ⟨τ, hτ, hστ, _⟩ :=
      Paper7PruningCanonical.dihedral_inverse 6 (by decide) σ hσ
    obtain ⟨μ, hμ, hpμ⟩ := (Paper7C61Orbit.dihedral_orbit_iff (p ∘ σ)).mpr hp
    apply (Paper7C61Orbit.dihedral_orbit_iff p).mp
    refine ⟨μ ∘ τ, Paper7PruningCanonical.dihedral_comp 6 (by decide) μ τ hμ hτ, ?_⟩
    funext k
    have hi : σ (τ k) = k := congrFun hστ k
    have hv := congrFun hpμ (τ k)
    change p (σ (τ k)) = C61P (μ (τ k)) at hv
    change p k = C61P (μ (τ k))
    rwa [hi] at hv
  · intro hp
    obtain ⟨μ, hμ, hpμ⟩ := (Paper7C61Orbit.dihedral_orbit_iff p).mpr hp
    apply (Paper7C61Orbit.dihedral_orbit_iff (p ∘ σ)).mp
    refine ⟨μ ∘ σ, Paper7PruningCanonical.dihedral_comp 6 (by decide) μ σ hμ hσ, ?_⟩
    funext k
    exact congrFun hpμ (σ k)
#print axioms Paper7C61Classification.rotations_comp_iff

theorem zero_comp_iff (q : Fin 6 → ℕ) (σ : Fin 6 → Fin 6)
    (hσ : IsDihedral 6 σ) : q ∘ σ = (fun _ => 0) ↔ q = (fun _ => 0) := by
  constructor
  · intro h
    funext k
    obtain ⟨j, rfl⟩ := (Paper7PruningCanonical.dihedral_bijective 6 (by decide) σ hσ).2 k
    exact congrFun h j
  · intro h
    subst q
    rfl
#print axioms Paper7C61Classification.zero_comp_iff

theorem nOf_comp (p q : Fin 6 → ℕ) (σ : Fin 6 → Fin 6)
    (hσ : IsDihedral 6 σ) : nOf 6 (p ∘ σ) (q ∘ σ) = nOf 6 p q := by
  have hbij := Paper7PruningCanonical.dihedral_bijective 6 (by decide) σ hσ
  have hp : (∑ k, (p ∘ σ) k) = ∑ k, p k := hbij.sum_comp p
  have hq : (∑ k, (q ∘ σ) k) = ∑ k, q k := hbij.sum_comp q
  simp only [nOf, hp, hq]
#print axioms Paper7C61Classification.nOf_comp

theorem pendant_sum_comp (p q : Fin 6 → ℕ) (σ : Fin 6 → Fin 6)
    (hσ : IsDihedral 6 σ) :
    (∑ k, ((p ∘ σ) k + (q ∘ σ) k)) = ∑ k, (p k + q k) := by
  exact (Paper7PruningCanonical.dihedral_bijective 6 (by decide) σ hσ).sum_comp
    (fun k => p k + q k)
#print axioms Paper7C61Classification.pendant_sum_comp

theorem integral_comp_iff (p q : Fin 6 → ℕ) (σ : Fin 6 → Fin 6)
    (hσ : IsDihedral 6 σ) :
    IsIntegralGraph (SG 6 (p ∘ σ) (q ∘ σ)) ↔ IsIntegralGraph (SG 6 p q) := by
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 6 p q (p ∘ σ) (q ∘ σ)
    (by decide) σ hσ rfl rfl
  exact ⟨Paper7Normalize.graphIso_integral _ _ e.symm,
    Paper7Normalize.graphIso_integral _ _ e⟩
#print axioms Paper7C61Classification.integral_comp_iff

end Paper7C61Classification
