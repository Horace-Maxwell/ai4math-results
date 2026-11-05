import Research.Backfill.Paper7.BMSSharpEndpoint
import Research.Backfill.Paper7.SpectralMoments

/-! A strict threshold-count drop preserves the closed sharp upper endpoint. -/
set_option autoImplicit false
noncomputable section
namespace Paper7BMS
open BackfillPaper7.Challenge

theorem exists_mem_Ioc_of_count_drop (s : Multiset ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcount : (s.filter (fun x => b < x)).card < (s.filter (fun x => a < x)).card) :
    ∃ x ∈ s, a < x ∧ x ≤ b := by
  classical
  by_contra hnone
  have heq : s.filter (fun x => a < x) = s.filter (fun x => b < x) := by
    apply Multiset.filter_congr
    intro x hx
    constructor
    · intro hax
      apply lt_of_not_ge
      intro hxb
      exact hnone ⟨x, hx, hax, hxb⟩
    · intro hbx
      exact lt_of_le_of_lt hab hbx
  rw [heq] at hcount
  exact (lt_irrefl _) hcount
#print axioms Paper7BMS.exists_mem_Ioc_of_count_drop

theorem graph_positive_interval_of_counts {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcount : Ngt G rho < Ngt G 1) : ∃ x ∈ spec G, 1 < x ∧ x ≤ rho :=
  exists_mem_Ioc_of_count_drop (spec G) 1 rho one_lt_rho.le hcount
#print axioms Paper7BMS.graph_positive_interval_of_counts

theorem sharp_positive_interval_not_integral {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∃ x ∈ spec G, 1 < x ∧ x ≤ rho) : ¬ IsIntegralGraph G := by
  intro hG
  obtain ⟨x, hx, hx1, hxrho⟩ := h
  obtain ⟨z, hz⟩ := Paper7Moments.integral_spec_entry G hG x hx
  have hzR : (1 : ℝ) < (z : ℝ) ∧ (z : ℝ) < 2 := by
    rw [← hz]
    exact ⟨hx1, hxrho.trans_lt rho_lt_two⟩
  have hzZ : (1 : ℤ) < z ∧ z < 2 := by exact_mod_cast hzR
  omega
#print axioms Paper7BMS.sharp_positive_interval_not_integral

end Paper7BMS
