import Research.Backfill.Paper7.B4SinglePDisjointRoots
import Research.Backfill.Paper7.ControlB4CertifiedReduction

/-! Source-only complete exclusion of arbitrary nonzero Q with exactly one
positive P site. The same-site and disjoint-Q cases both give an open-unit root. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem single_p_same_site_q_small_root (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hq0 : 0 < q 0) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      singlePMixedPolynomial (p 0) (q 0) (q 1) (q 2) (q 3) t = 0 := by
  obtain ⟨r,hr0,_hrle,hAr,hrstrict⟩ := mixed_local_small_root (p 0) (q 0) hp0
  have hr1 : r < 1 := hrstrict hq0
  change r^2-((p 0 : ℝ)+q 0+1)*r+p 0 = 0 at hAr
  let K : ℝ → ℝ := singlePMixedPolynomial (p 0) (q 0) (q 1) (q 2) (q 3)
  have hK0eq : K 0 = (p 0 : ℝ)*((q 1 : ℝ)+q 3+2) := by
    dsimp [K,singlePMixedPolynomial]; ring
  have hp0R : (0 : ℝ) < p 0 := by exact_mod_cast hp0
  have hK0 : 0 < K 0 := by rw [hK0eq]; positivity
  have hD : r-(q 2 : ℝ)-1 < 0 := by have hh : (0 : ℝ) ≤ q 2 := Nat.cast_nonneg _; linarith
  have hS : 2*r-(q 1 : ℝ)-q 3-2 < 0 := by
    have h1 : (0 : ℝ) ≤ q 1 := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ q 3 := Nat.cast_nonneg _
    linarith
  have hsquare : 0 < (r-1)^2 := sq_pos_of_ne_zero (by linarith)
  have hprod : 0 < (r-1)^2*((r*(r-(q 2 : ℝ)-1))*(2*r-(q 1 : ℝ)-q 3-2)) :=
    mul_pos hsquare (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hr0 hD) hS)
  have hKreq : K r = -(r-1)^2*(r*(r-(q 2 : ℝ)-1))*(2*r-(q 1 : ℝ)-q 3-2) := by
    dsimp [K,singlePMixedPolynomial]
    rw [hAr]
    ring
  have hKr : K r < 0 := by nlinarith only [hKreq,hprod]
  have hcont : Continuous (fun t : ℝ => -K t) := by dsimp [K,singlePMixedPolynomial]; fun_prop
  have hzero : (0 : ℝ) ∈ Set.Ioo (-K 0) (-K r) := ⟨by linarith,by linarith⟩
  obtain ⟨t,ht,hft⟩ := intermediate_value_Ioo hr0.le hcont.continuousOn hzero
  have htK : K t = 0 := by linarith only [hft]
  exact ⟨t,ht.1,ht.2.trans hr1,htK⟩
#print axioms Paper7B4Analytic.single_p_same_site_q_small_root

theorem single_p_mixed_nonintegral (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : p 1 = 0) (hp2 : p 2 = 0) (hp3 : p 3 = 0)
    (hq : 0 < ∑ i, q i) : ¬ IsIntegralGraph (SG 4 p q) := by
  have hex : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      singlePMixedPolynomial (p 0) (q 0) (q 1) (q 2) (q 3) t = 0 := by
    by_cases hq0 : q 0 = 0
    · have hqpos : 0 < (q 1+q 3)+q 2 := by rw [Fin.sum_univ_four,hq0] at hq; omega
      obtain ⟨t,ht0,ht1,hft⟩ := single_p_disjoint_small_root (p 0) (q 1+q 3)
        (q 1*q 3) (q 2) hp0 hqpos
      refine ⟨t,ht0,ht1,?_⟩
      rw [hq0]
      norm_num only [Nat.cast_zero]
      rw [single_p_disjoint_factor]
      simpa only [Nat.cast_add,Nat.cast_mul] using hft
    · exact single_p_same_site_q_small_root p q hp0 (Nat.pos_of_ne_zero hq0)
  obtain ⟨t,ht0,ht1,hft⟩ := hex
  have he : mixedPolynomial p q t = 0 := by
    rw [single_p_mixed_factor p q hp1 hp2 hp3 t,hft,mul_zero]
  exact mixed_small_root_nonintegral p q t ht0 ht1 he
#print axioms Paper7B4Analytic.single_p_mixed_nonintegral

theorem single_p_site_mixed_nonintegral (p q : Fin 4 → ℕ) (i : Fin 4)
    (hpi : 0 < p i) (hp : ∀ j : Fin 4, j ≠ i → p j = 0)
    (hq : 0 < ∑ j, q j) : ¬ IsIntegralGraph (SG 4 p q) := by
  intro hG
  let σ : Fin 4 → Fin 4 := fun k => k+i
  have hσ : IsDihedral 4 σ := by
    refine ⟨i,Or.inl ?_⟩
    intro k
    fin_cases i <;> fin_cases k <;> decide
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 p q (p ∘ σ) (q ∘ σ)
    (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hsum : ∑ j, (q ∘ σ) j = ∑ j, q j :=
    (Paper7PruningCanonical.dihedral_bijective 4 (by decide) σ hσ).sum_comp q
  have hq' : 0 < ∑ j, (q ∘ σ) j := by rw [hsum]; exact hq
  have h0 : 0 < (p ∘ σ) 0 := by simpa [σ] using hpi
  have h1 : (p ∘ σ) 1 = 0 := by apply hp; fin_cases i <;> decide
  have h2 : (p ∘ σ) 2 = 0 := by apply hp; fin_cases i <;> decide
  have h3 : (p ∘ σ) 3 = 0 := by apply hp; fin_cases i <;> decide
  exact single_p_mixed_nonintegral (p ∘ σ) (q ∘ σ) h0 h1 h2 h3 hq' hI
#print axioms Paper7B4Analytic.single_p_site_mixed_nonintegral

theorem original_single_p_mixed_nonintegral (L : Fin 4 → List ℕ) (i : Fin 4)
    (hpi : 0 < Paper7Normalize.countP1 4 L i)
    (hp : ∀ j : Fin 4, j ≠ i → Paper7Normalize.countP1 4 L j = 0)
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
  exact single_p_site_mixed_nonintegral p q i hpi hp hq hI
#print axioms Paper7B4Analytic.original_single_p_mixed_nonintegral

end Paper7B4Analytic
