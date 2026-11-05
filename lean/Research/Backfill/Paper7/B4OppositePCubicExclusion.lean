import Research.Backfill.Paper7.B4SimplePositiveSpectrum
import Research.Backfill.Paper7.B4OppositePThreeRootArithmetic

/-! Source-only exclusion of the three-root cubic configurations by the
actual order bound and exact integer coefficient identities. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge

theorem opposite_cubic_profile_impossible (T E D z : ℤ) (r s t : ℕ)
    (hr : 2 ≤ r) (hrs : r < s) (hst : s < t) (hbudget : r^2+s^2+t^2 ≤ 49)
    (hrel : z^3+(3-T)*z^2+(E-T+1)*z+T-4-D = 0)
    (hroot : ∀ m ∈ ({r,s,t} : Finset ℕ),
      (m : ℝ)^6-(T : ℝ)*(m : ℝ)^4+(E : ℝ)*(m : ℝ)^2-D = 0) : False := by
  have hprof := ordered_three_square_profiles r s t hr hrs hst hbudget
  rcases hprof with ⟨rfl,rfl,ht⟩ | ⟨rfl,rfl,rfl⟩
  · rcases ht with rfl | rfl | rfl
    · have h2 := hroot 2 (by simp)
      have h3 := hroot 3 (by simp)
      have h4 := hroot 4 (by simp)
      norm_num at h2 h3 h4
      have hTR : (T : ℝ) = 29 := by linarith only [h2,h3,h4]
      have hER : (E : ℝ) = 244 := by linarith only [h2,h3,h4]
      have hDR : (D : ℝ) = 576 := by linarith only [h2,h3,h4]
      have hT : T = 29 := by exact_mod_cast hTR
      have hE : E = 244 := by exact_mod_cast hER
      have hD : D = 576 := by exact_mod_cast hDR
      rw [hT,hE,hD] at hrel
      norm_num at hrel
      exact opposite_three_root_234_impossible z (by nlinarith only [hrel])
    · have h2 := hroot 2 (by simp)
      have h3 := hroot 3 (by simp)
      have h5 := hroot 5 (by simp)
      norm_num at h2 h3 h5
      have hTR : (T : ℝ) = 38 := by linarith only [h2,h3,h5]
      have hER : (E : ℝ) = 361 := by linarith only [h2,h3,h5]
      have hDR : (D : ℝ) = 900 := by linarith only [h2,h3,h5]
      have hT : T = 38 := by exact_mod_cast hTR
      have hE : E = 361 := by exact_mod_cast hER
      have hD : D = 900 := by exact_mod_cast hDR
      rw [hT,hE,hD] at hrel
      norm_num at hrel
      exact opposite_three_root_235_impossible z (by nlinarith only [hrel])
    · have h2 := hroot 2 (by simp)
      have h3 := hroot 3 (by simp)
      have h6 := hroot 6 (by simp)
      norm_num at h2 h3 h6
      have hTR : (T : ℝ) = 49 := by linarith only [h2,h3,h6]
      have hER : (E : ℝ) = 504 := by linarith only [h2,h3,h6]
      have hDR : (D : ℝ) = 1296 := by linarith only [h2,h3,h6]
      have hT : T = 49 := by exact_mod_cast hTR
      have hE : E = 504 := by exact_mod_cast hER
      have hD : D = 1296 := by exact_mod_cast hDR
      rw [hT,hE,hD] at hrel
      norm_num at hrel
      exact opposite_three_root_236_impossible z (by nlinarith only [hrel])
  · have h2 := hroot 2 (by simp)
    have h4 := hroot 4 (by simp)
    have h5 := hroot 5 (by simp)
    norm_num at h2 h4 h5
    have hTR : (T : ℝ) = 45 := by linarith only [h2,h4,h5]
    have hER : (E : ℝ) = 564 := by linarith only [h2,h4,h5]
    have hDR : (D : ℝ) = 1600 := by linarith only [h2,h4,h5]
    have hT : T = 45 := by exact_mod_cast hTR
    have hE : E = 564 := by exact_mod_cast hER
    have hD : D = 1600 := by exact_mod_cast hDR
    rw [hT,hE,hD] at hrel
    norm_num at hrel
    exact opposite_three_root_245_impossible z (by nlinarith only [hrel])
#print axioms Paper7B4Analytic.opposite_cubic_profile_impossible

theorem opposite_spectral_cubic_impossible (p q : Fin 4 → ℕ)
    (hn : nOf 4 p q ≤ 49) (hG : IsIntegralGraph (SG 4 p q))
    (hm : ∀ x : ℝ, 2 ≤ x → mult (SG 4 p q) x ≤ 1)
    (hcard : (Bplus (SG 4 p q)).card = 3) (T E D z : ℤ)
    (hrel : z^3+(3-T)*z^2+(E-T+1)*z+T-4-D = 0)
    (hroot : ∀ m : ℝ, 2 ≤ m → m ∈ spec (SG 4 p q) →
      m^6-(T : ℝ)*m^4+(E : ℝ)*m^2-D = 0) : False := by
  obtain ⟨r,s,t,hr,hrs,hst,hbudget,hrm,hsm,htm⟩ :=
    simple_positive_three_integer_roots p q hn hG hm hcard
  apply opposite_cubic_profile_impossible T E D z r s t hr hrs hst hbudget hrel
  intro m hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hmr | hms | hmt
  · rw [hmr]
    exact hroot r (by exact_mod_cast hr) hrm
  · rw [hms]
    exact hroot s (by exact_mod_cast (show 2 ≤ s by omega)) hsm
  · rw [hmt]
    exact hroot t (by exact_mod_cast (show 2 ≤ t by omega)) htm
#print axioms Paper7B4Analytic.opposite_spectral_cubic_impossible

end Paper7B4Analytic
