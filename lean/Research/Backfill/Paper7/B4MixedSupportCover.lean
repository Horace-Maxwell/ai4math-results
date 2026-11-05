import Research.Backfill.Paper7.B4MixedPSupportReduction

/-! Source-only exhaustive support reduction on the actual four vertices.
The support cases are conclusions of the cardinality equation. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem mixed_support_card_four (p : Fin 4 → ℕ) :
    (Kp 4 p).card = (if 0 < p 0 then 1 else 0)+(if 0 < p 1 then 1 else 0)+
      (if 0 < p 2 then 1 else 0)+(if 0 < p 3 then 1 else 0) := by
  rw [Kp,Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_four]
#print axioms Paper7B4Analytic.mixed_support_card_four

theorem mixed_support_rotation_dihedral (i : Fin 4) :
    IsDihedral 4 (fun k : Fin 4 => k+i) := by
  refine ⟨i,Or.inl ?_⟩
  intro k
  fin_cases i <;> fin_cases k <;> decide
#print axioms Paper7B4Analytic.mixed_support_rotation_dihedral

theorem mixed_two_support_dihedral_cases (p : Fin 4 → ℕ) (hcard : (Kp 4 p).card = 2) :
    ∃ σ : Fin 4 → Fin 4, IsDihedral 4 σ ∧
      ((0 < p (σ 0) ∧ 0 < p (σ 1) ∧ p (σ 2) = 0 ∧ p (σ 3) = 0) ∨
       (0 < p (σ 0) ∧ p (σ 1) = 0 ∧ 0 < p (σ 2) ∧ p (σ 3) = 0)) := by
  have hcount := mixed_support_card_four p
  rw [hcard] at hcount
  have hcases :
      (0 < p 0 ∧ 0 < p 1 ∧ p 2 = 0 ∧ p 3 = 0) ∨
      (0 < p 0 ∧ p 1 = 0 ∧ 0 < p 2 ∧ p 3 = 0) ∨
      (0 < p 0 ∧ p 1 = 0 ∧ p 2 = 0 ∧ 0 < p 3) ∨
      (p 0 = 0 ∧ 0 < p 1 ∧ 0 < p 2 ∧ p 3 = 0) ∨
      (p 0 = 0 ∧ 0 < p 1 ∧ p 2 = 0 ∧ 0 < p 3) ∨
      (p 0 = 0 ∧ p 1 = 0 ∧ 0 < p 2 ∧ 0 < p 3) := by
    split_ifs at hcount <;> omega
  rcases hcases with h | h | h | h | h | h
  · refine ⟨fun k => k+(0 : Fin 4),mixed_support_rotation_dihedral 0,Or.inl ?_⟩
    norm_num; omega
  · refine ⟨fun k => k+(0 : Fin 4),mixed_support_rotation_dihedral 0,Or.inr ?_⟩
    norm_num; omega
  · refine ⟨fun k => k+(3 : Fin 4),mixed_support_rotation_dihedral 3,Or.inl ?_⟩
    norm_num; omega
  · refine ⟨fun k => k+(1 : Fin 4),mixed_support_rotation_dihedral 1,Or.inl ?_⟩
    norm_num; omega
  · refine ⟨fun k => k+(1 : Fin 4),mixed_support_rotation_dihedral 1,Or.inr ?_⟩
    norm_num; omega
  · refine ⟨fun k => k+(2 : Fin 4),mixed_support_rotation_dihedral 2,Or.inl ?_⟩
    norm_num; omega
#print axioms Paper7B4Analytic.mixed_two_support_dihedral_cases

theorem mixed_three_support_dihedral_case (p : Fin 4 → ℕ) (hcard : (Kp 4 p).card = 3) :
    ∃ σ : Fin 4 → Fin 4, IsDihedral 4 σ ∧
      0 < p (σ 0) ∧ 0 < p (σ 1) ∧ 0 < p (σ 2) ∧ p (σ 3) = 0 := by
  have hcount := mixed_support_card_four p
  rw [hcard] at hcount
  have hcases :
      (p 0 = 0 ∧ 0 < p 1 ∧ 0 < p 2 ∧ 0 < p 3) ∨
      (0 < p 0 ∧ p 1 = 0 ∧ 0 < p 2 ∧ 0 < p 3) ∨
      (0 < p 0 ∧ 0 < p 1 ∧ p 2 = 0 ∧ 0 < p 3) ∨
      (0 < p 0 ∧ 0 < p 1 ∧ 0 < p 2 ∧ p 3 = 0) := by
    split_ifs at hcount <;> omega
  rcases hcases with h | h | h | h
  · refine ⟨fun k => k+(1 : Fin 4),mixed_support_rotation_dihedral 1,?_⟩
    norm_num; omega
  · refine ⟨fun k => k+(2 : Fin 4),mixed_support_rotation_dihedral 2,?_⟩
    norm_num; omega
  · refine ⟨fun k => k+(3 : Fin 4),mixed_support_rotation_dihedral 3,?_⟩
    norm_num; omega
  · refine ⟨fun k => k+(0 : Fin 4),mixed_support_rotation_dihedral 0,?_⟩
    norm_num; omega
#print axioms Paper7B4Analytic.mixed_three_support_dihedral_case

end Paper7B4Analytic
