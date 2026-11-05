import Research.Backfill.Paper7.B4ThreePSpectralRank
import Research.Backfill.Paper7.B4ThreeRootArithmetic
import Research.Backfill.Paper7.B4OppositeBranch

/-! Source-only complete three-positive-site exclusion in order at most 49.
The four root profiles are consequences of actual integral, simple spectrum. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem three_positive_nonintegral (p : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : 0 < p 2) (hp3 : p 3 = 0)
    (hn : nOf 4 p (fun _ => 0) ≤ 49) :
    ¬ IsIntegralGraph (SG 4 p (fun _ => 0)) := by
  intro hG
  obtain ⟨r,s,t,hr,hrs,hst,hsum,hrm,hsm,htm⟩ :=
    three_positive_integer_roots p hp0 hp1 hp2 hp3 hn hG
  have hroots (k : ℕ) (hk : 2 ≤ k) (hkm : (k : ℝ) ∈ spec (SG 4 p (fun _ => 0))) :
      threePCubic (p 0) (p 1) (p 2) ((k : ℝ)^2) = 0 := by
    have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
    exact (three_p_ordinary_spec_iff p hp3 k (by linarith) (by linarith)
      (by linarith)).mp hkm
  rcases ordered_three_square_profiles r s t hr hrs hst hsum with
    ⟨rfl,rfl,ht⟩ | ⟨rfl,rfl,rfl⟩
  · have h2 := hroots 2 (by decide) hrm
    have h3 := hroots 3 (by decide) hsm
    rcases ht with rfl | rfl | rfl
    · have h4 := hroots 4 (by decide) htm
      norm_num [threePCubic] at h2 h3 h4
      have hT : (p 0 : ℝ)+p 1+p 2+4 = 29 := by nlinarith only [h2,h3,h4]
      have hE : (p 0 : ℝ)*p 1+(p 0 : ℝ)*p 2+(p 1 : ℝ)*p 2+
          2*((p 0 : ℝ)+p 1+p 2) = 244 := by nlinarith only [h2,h3,h4]
      have hD : (p 1 : ℝ)*((p 0 : ℝ)*p 2+p 0+p 2) = 576 := by nlinarith only [h2,h3,h4]
      exact three_root_234_impossible (p 0) (p 1) (p 2) hp0 hp1 hp2
        (by exact_mod_cast hT) (by exact_mod_cast hE) (by exact_mod_cast hD)
    · have h5 := hroots 5 (by decide) htm
      norm_num [threePCubic] at h2 h3 h5
      have hT : (p 0 : ℝ)+p 1+p 2+4 = 38 := by nlinarith only [h2,h3,h5]
      have hE : (p 0 : ℝ)*p 1+(p 0 : ℝ)*p 2+(p 1 : ℝ)*p 2+
          2*((p 0 : ℝ)+p 1+p 2) = 361 := by nlinarith only [h2,h3,h5]
      have hD : (p 1 : ℝ)*((p 0 : ℝ)*p 2+p 0+p 2) = 900 := by nlinarith only [h2,h3,h5]
      exact three_root_235_impossible (p 0) (p 1) (p 2) hp0 hp1 hp2
        (by exact_mod_cast hT) (by exact_mod_cast hE) (by exact_mod_cast hD)
    · have h6 := hroots 6 (by decide) htm
      norm_num [threePCubic] at h2 h3 h6
      have hT : (p 0 : ℝ)+p 1+p 2+4 = 49 := by nlinarith only [h2,h3,h6]
      have hE : (p 0 : ℝ)*p 1+(p 0 : ℝ)*p 2+(p 1 : ℝ)*p 2+
          2*((p 0 : ℝ)+p 1+p 2) = 504 := by nlinarith only [h2,h3,h6]
      have hD : (p 1 : ℝ)*((p 0 : ℝ)*p 2+p 0+p 2) = 1296 := by nlinarith only [h2,h3,h6]
      exact three_root_236_impossible (p 0) (p 1) (p 2) hp0 hp1 hp2
        (by exact_mod_cast hT) (by exact_mod_cast hE) (by exact_mod_cast hD)
  · have h2 := hroots 2 (by decide) hrm
    have h4 := hroots 4 (by decide) hsm
    have h5 := hroots 5 (by decide) htm
    norm_num [threePCubic] at h2 h4 h5
    have hT : (p 0 : ℝ)+p 1+p 2+4 = 45 := by nlinarith only [h2,h4,h5]
    have hE : (p 0 : ℝ)*p 1+(p 0 : ℝ)*p 2+(p 1 : ℝ)*p 2+
        2*((p 0 : ℝ)+p 1+p 2) = 564 := by nlinarith only [h2,h4,h5]
    have hD : (p 1 : ℝ)*((p 0 : ℝ)*p 2+p 0+p 2) = 1600 := by nlinarith only [h2,h4,h5]
    exact three_root_245_impossible (p 0) (p 1) (p 2) hp0 hp1 hp2
      (by exact_mod_cast hT) (by exact_mod_cast hE) (by exact_mod_cast hD)
#print axioms Paper7B4Analytic.three_positive_nonintegral

theorem three_positive_dihedral_nonintegral (p : Fin 4 → ℕ)
    (hn : nOf 4 p (fun _ => 0) ≤ 49)
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (hp0 : 0 < (p ∘ σ) 0) (hp1 : 0 < (p ∘ σ) 1)
    (hp2 : 0 < (p ∘ σ) 2) (hp3 : (p ∘ σ) 3 = 0) :
    ¬ IsIntegralGraph (SG 4 p (fun _ => 0)) := by
  intro hG
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 p (fun _ => 0)
    (p ∘ σ) (fun _ => 0) (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hsum : ∑ k, (p ∘ σ) k = ∑ k, p k :=
    (Paper7PruningCanonical.dihedral_bijective 4 (by decide) σ hσ).sum_comp p
  have hn' : nOf 4 (p ∘ σ) (fun _ => 0) ≤ 49 := by
    simpa only [nOf,hsum] using hn
  exact three_positive_nonintegral (p ∘ σ) hp0 hp1 hp2 hp3 hn' hI
#print axioms Paper7B4Analytic.three_positive_dihedral_nonintegral

end Paper7B4Analytic
