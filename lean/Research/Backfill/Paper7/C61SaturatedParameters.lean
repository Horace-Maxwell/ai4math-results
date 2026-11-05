import Research.Backfill.Paper7.C61ParameterSquares

/-! Analytic exclusion of the two remaining positive-Q cases in the actual
five-entry spectral branch. No finite table or classification assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Parameters
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile
open scoped BigOperators Classical

theorem saturated_totalQ_zero (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (hc : card (actual p q) = 5) : totalQ 6 q = 0 := by
  obtain ⟨hm, _horder, _hunit, hQ, hPQ, _ha, _he, _hpoly⟩ :=
    saturated_profile_parameters p q hp hn hG hc
  have hsupport := saturated_support_bound p q hp hn hG hc
  have htheta := profile_parameter_moment p q hn hG
  rw [hm, fourth_c61] at htheta
  have hthetaN : squares 6 (fun k => p k + q k) +
      3 * (totalP 6 p + totalQ 6 q) + 12 + 2 * totalQ 6 q = 408 := by
    exact_mod_cast htheta.symm
  have hload := load_squares_lower 6 p q
  have hsq : squares 6 p ≤ 288 := by omega
  have hcs := support_cauchy 6 p
  have hmul : (Kp 6 p).card * squares 6 p ≤ (Kp 6 p).card * 288 :=
    Nat.mul_le_mul_left _ hsq
  by_contra hzero
  have hcases : totalQ 6 q = 1 ∨ totalQ 6 q = 2 := by omega
  rcases hcases with hq1 | hq2
  · have hP : totalP 6 p = 34 := by omega
    have hK : (Kp 6 p).card ≤ 4 := by omega
    have hbound := Nat.mul_le_mul_right 288 hK
    rw [hP] at hcs
    omega
  · have hP : totalP 6 p = 32 := by omega
    have hK : (Kp 6 p).card ≤ 3 := by omega
    have hbound := Nat.mul_le_mul_right 288 hK
    rw [hP] at hcs
    omega
#print axioms Paper7C61Parameters.saturated_totalQ_zero

theorem saturated_parameter_data (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (hc : card (actual p q) = 5) :
    q = (fun _ => 0) ∧ totalP 6 p = 36 ∧ squares 6 p = 288 ∧ (Kp 6 p).card = 5 := by
  have hQ := saturated_totalQ_zero p q hp hn hG hc
  have hq := zero_of_totalQ_zero 6 q hQ
  obtain ⟨hm, _horder, _hunit, _hQ, hPQ, _ha, _he, _hpoly⟩ :=
    saturated_profile_parameters p q hp hn hG hc
  have htheta := profile_parameter_moment p q hn hG
  rw [hm, fourth_c61, hQ] at htheta
  have hP : totalP 6 p = 36 := by omega
  have hload : squares 6 (fun k => p k + q k) = squares 6 p := by simp [hq]
  have hS : squares 6 p = 288 := by
    rw [hload, hP] at htheta
    norm_num at htheta
    exact_mod_cast (by linarith : (squares 6 p : ℤ) = 288)
  have hsupport := saturated_support_bound p q hp hn hG hc
  have hcs := support_cauchy 6 p
  rw [hP, hS] at hcs
  refine ⟨hq, hP, hS, ?_⟩
  omega
#print axioms Paper7C61Parameters.saturated_parameter_data

theorem positive_coordinate_interval (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 36) (hS : squares 6 p = 288) (hK : (Kp 6 p).card = 5)
    (k : Fin 6) (hk : 0 < p k) : 3 ≤ p k ∧ p k ≤ 12 := by
  have hmem : k ∈ Kp 6 p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  have hsum := Finset.sum_erase_add (Kp 6 p) p hmem
  have hsq := Finset.sum_erase_add (Kp 6 p) (fun j => p j ^ 2) hmem
  rw [support_sum, hP] at hsum
  rw [support_squares, hS] at hsq
  have hcard : ((Kp 6 p).erase k).card = 4 := by
    rw [Finset.card_erase_of_mem hmem, hK]
  have hcs := cauchy_on ((Kp 6 p).erase k) p
  rw [hcard] at hcs
  let A : ℕ := ∑ j ∈ (Kp 6 p).erase k, p j
  let B : ℕ := ∑ j ∈ (Kp 6 p).erase k, p j ^ 2
  have hsumR : (A : ℝ) + (p k : ℝ) = 36 := by exact_mod_cast hsum
  have hsqR : (B : ℝ) + (p k : ℝ) ^ 2 = 288 := by exact_mod_cast hsq
  have hcsR : (A : ℝ) ^ 2 ≤ 4 * (B : ℝ) := by exact_mod_cast hcs
  have hA : (A : ℝ) = 36 - (p k : ℝ) := by linarith
  rw [hA] at hcsR
  have hpolyR : (5 : ℝ) * (p k : ℝ) ^ 2 + 144 ≤ 72 * (p k : ℝ) := by
    nlinarith
  constructor
  · by_contra h
    have hsmall : (p k : ℝ) ≤ 2 := by exact_mod_cast (show p k ≤ 2 by omega)
    nlinarith [sq_nonneg ((p k : ℝ) - 2)]
  · by_contra h
    have hlarge : (13 : ℝ) ≤ p k := by exact_mod_cast (show 13 ≤ p k by omega)
    nlinarith [sq_nonneg ((p k : ℝ) - 13)]
#print axioms Paper7C61Parameters.positive_coordinate_interval

theorem unique_zero_of_support_five (p : Fin 6 → ℕ) (hK : (Kp 6 p).card = 5) :
    ∃! k, p k = 0 := by
  have hcard : ((Kp 6 p)ᶜ).card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin, hK]
  obtain ⟨k, hk, huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp hcard
  have hzero (j : Fin 6) : j ∈ (Kp 6 p)ᶜ ↔ p j = 0 := by
    simp only [Finset.mem_compl, Kp, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  refine ⟨k, (hzero k).mp hk, ?_⟩
  intro j hj
  exact huniq j ((hzero j).mpr hj)
#print axioms Paper7C61Parameters.unique_zero_of_support_five

/-- Normalize the unique p-zero only after q=0 has been derived. This does not
assume coincident zero positions in any original arbitrary p,q tuple. -/
theorem saturated_normalized_parameters (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (hc : card (actual p q) = 5) :
    q = (fun _ => 0) ∧ ∃ σ : Fin 6 → Fin 6, IsDihedral 6 σ ∧ (p ∘ σ) 0 = 0 ∧
      (∀ k, k ≠ 0 → 3 ≤ (p ∘ σ) k ∧ (p ∘ σ) k ≤ 12) ∧
      totalP 6 (p ∘ σ) = 36 ∧ squares 6 (p ∘ σ) = 288 ∧
      IsIntegralGraph (SG 6 (p ∘ σ) (fun _ => 0)) := by
  obtain ⟨hq, hP, hS, hK⟩ := saturated_parameter_data p q hp hn hG hc
  obtain ⟨j, hj, huniq⟩ := unique_zero_of_support_five p hK
  obtain ⟨σ, hσ, hσ0⟩ :=
    Paper7PruningCanonical.dihedral_rotation_to 6 (by decide) j 0 rfl
  have hbij := Paper7PruningCanonical.dihedral_bijective 6 (by decide) σ hσ
  refine ⟨hq, σ, hσ, ?_, ?_, ?_, ?_, ?_⟩
  · change p (σ 0) = 0
    rwa [hσ0]
  · intro k hk
    apply positive_coordinate_interval p hP hS hK (σ k)
    have hne : p (σ k) ≠ 0 := by
      intro hz
      have hj' := huniq (σ k) hz
      have heq : σ k = σ 0 := hj'.trans hσ0.symm
      exact hk (hbij.1 heq)
    omega
  · exact (hbij.sum_comp p).trans hP
  · exact (hbij.sum_comp (fun k => p k ^ 2)).trans hS
  · have h := (Paper7C61Classification.integral_comp_iff p q σ hσ).mpr hG
    change IsIntegralGraph (SG 6 (p ∘ σ) (q ∘ σ)) at h
    rw [hq] at h
    exact h
#print axioms Paper7C61Parameters.saturated_normalized_parameters

end Paper7C61Parameters
