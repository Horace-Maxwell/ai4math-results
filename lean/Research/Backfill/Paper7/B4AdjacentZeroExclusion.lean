import Research.Backfill.Paper7.B4AdjacentPExclusion
import Research.Backfill.Paper7.B4OppositeBranch

/-! Source-only completion of the q=0 branch with two adjacent zero sites,
including all one-site support cases. No order bound is needed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Matrix Classical

theorem qzero_adjacent_zeros_nonintegral (p : Fin 4 → ℕ)
    (hp : 0 < ∑ k, (p k+(0 : ℕ))) (hp2 : p 2 = 0) (hp3 : p 3 = 0) :
    ¬ IsIntegralGraph (SG 4 p (fun _ => 0)) := by
  intro hG
  by_cases hp1 : p 1 = 0
  · rcases opposite_integral_parameters p hp hG hp1 hp3 with h | h
    · omega
    · omega
  by_cases hp0 : p 0 = 0
  · let σ : Fin 4 → Fin 4 := fun k => k+1
    have hσ : IsDihedral 4 σ := by
      refine ⟨1,Or.inl ?_⟩
      intro k
      fin_cases k <;> decide
    obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 p (fun _ => 0)
      (p ∘ σ) (fun _ => 0) (by decide) σ hσ rfl rfl
    have hI := Paper7Normalize.graphIso_integral _ _ e hG
    have hsum : ∑ k, (p ∘ σ) k = ∑ k, p k :=
      (Paper7PruningCanonical.dihedral_bijective 4 (by decide) σ hσ).sum_comp p
    have hp' : 0 < ∑ k, ((p ∘ σ) k+(0 : ℕ)) := by
      simpa only [Nat.add_zero,hsum] using hp
    have h1 : (p ∘ σ) 1 = 0 := by change p 2 = 0; exact hp2
    have h2 : (p ∘ σ) 2 = 0 := by change p 3 = 0; exact hp3
    have h3 : (p ∘ σ) 3 = 0 := by change p 0 = 0; exact hp0
    rcases opposite_integral_parameters (p ∘ σ) hp' hI h1 h3 with h | h
    · omega
    · omega
  exact adjacent_positive_p_nonintegral p (by omega) (by omega) hp2 hp3 hG
#print axioms Paper7B4Analytic.qzero_adjacent_zeros_nonintegral

theorem qzero_dihedral_adjacent_zeros_nonintegral (p : Fin 4 → ℕ)
    (hp : 0 < ∑ k, (p k+(0 : ℕ)))
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (h2 : (p ∘ σ) 2 = 0) (h3 : (p ∘ σ) 3 = 0) :
    ¬ IsIntegralGraph (SG 4 p (fun _ => 0)) := by
  intro hG
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 p (fun _ => 0)
    (p ∘ σ) (fun _ => 0) (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hsum : ∑ k, (p ∘ σ) k = ∑ k, p k :=
    (Paper7PruningCanonical.dihedral_bijective 4 (by decide) σ hσ).sum_comp p
  have hp' : 0 < ∑ k, ((p ∘ σ) k+(0 : ℕ)) := by
    simpa only [Nat.add_zero,hsum] using hp
  exact qzero_adjacent_zeros_nonintegral (p ∘ σ) hp' h2 h3 hI
#print axioms Paper7B4Analytic.qzero_dihedral_adjacent_zeros_nonintegral

theorem qzero_two_zero_sites_iso_g13 (p : Fin 4 → ℕ)
    (hp : 0 < ∑ k, (p k+(0 : ℕ))) (hG : IsIntegralGraph (SG 4 p (fun _ => 0)))
    (i j : Fin 4) (hne : i ≠ j) (hi : p i = 0) (hj : p j = 0) :
    Nonempty (SG 4 p (fun _ => 0) ≃g sunGraph 4 G13) := by
  have hcases : (p 0 = 0 ∧ p 1 = 0) ∨ (p 0 = 0 ∧ p 2 = 0) ∨
      (p 0 = 0 ∧ p 3 = 0) ∨ (p 1 = 0 ∧ p 2 = 0) ∨
      (p 1 = 0 ∧ p 3 = 0) ∨ (p 2 = 0 ∧ p 3 = 0) := by
    fin_cases i <;> fin_cases j <;> simp_all
  have hrot (c : Fin 4) : IsDihedral 4 (fun k : Fin 4 => k+c) := by
    refine ⟨c,Or.inl ?_⟩
    intro k
    fin_cases c <;> fin_cases k <;> decide
  rcases hcases with h | h | h | h | h | h
  · exact False.elim (qzero_dihedral_adjacent_zeros_nonintegral p hp
      (fun k => k+2) (hrot 2) (by change p 0 = 0; exact h.1)
      (by change p 1 = 0; exact h.2) hG)
  · exact opposite_dihedral_integral_iso_g13 p (fun _ => 0) hp hG rfl
      (fun k => k+3) (hrot 3) (by change p 0 = 0; exact h.1)
      (by change p 2 = 0; exact h.2)
  · exact False.elim (qzero_dihedral_adjacent_zeros_nonintegral p hp
      (fun k => k+1) (hrot 1) (by change p 3 = 0; exact h.2)
      (by change p 0 = 0; exact h.1) hG)
  · exact False.elim (qzero_dihedral_adjacent_zeros_nonintegral p hp
      (fun k => k+3) (hrot 3) (by change p 1 = 0; exact h.1)
      (by change p 2 = 0; exact h.2) hG)
  · exact opposite_integral_iso_g13 p hp hG h.1 h.2
  · exact False.elim (qzero_adjacent_zeros_nonintegral p hp h.1 h.2 hG)
#print axioms Paper7B4Analytic.qzero_two_zero_sites_iso_g13

end Paper7B4Analytic
