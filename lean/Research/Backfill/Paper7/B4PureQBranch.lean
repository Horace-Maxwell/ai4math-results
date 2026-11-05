import Research.Backfill.Paper7.B4PureQSupportExclusion
import Research.Backfill.Paper7.B4QOppositeBranch
import Research.Backfill.Paper7.B4QAdjacentBranch

/-! Source-only complete P=0 branch of the frozen b=4 classification.
The Q support coverage is proved, and the order bound is used only in the
already selected adjacent-Q arithmetic classification. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem pure_q_integral_named (q : Fin 4 → ℕ)
    (hq : 0 < ∑ k, q k) (hn : nOf 4 (fun _ => 0) q ≤ 49)
    (hG : IsIntegralGraph (SG 4 (fun _ => 0) q)) :
    Nonempty (SG 4 (fun _ => 0) q ≃g sunGraph 4 G20b) ∨
      Nonempty (SG 4 (fun _ => 0) q ≃g sunGraph 4 C42Ten) := by
  obtain ⟨i,j,hne,hi,hj⟩ := pure_q_integral_two_zero_sites q hG
  have hcases : (q 0 = 0 ∧ q 1 = 0) ∨ (q 0 = 0 ∧ q 2 = 0) ∨
      (q 0 = 0 ∧ q 3 = 0) ∨ (q 1 = 0 ∧ q 2 = 0) ∨
      (q 1 = 0 ∧ q 3 = 0) ∨ (q 2 = 0 ∧ q 3 = 0) := by
    fin_cases i <;> fin_cases j <;> simp_all
  have hrot (c : Fin 4) : IsDihedral 4 (fun k : Fin 4 => k+c) := by
    refine ⟨c,Or.inl ?_⟩
    intro k
    fin_cases c <;> fin_cases k <;> decide
  have hpq : 0 < ∑ k, ((0 : ℕ)+q k) := by simpa using hq
  rcases hcases with h | h | h | h | h | h
  · exact qadjacent_dihedral_integral_named (fun _ => 0) q hpq hn hG rfl
      (fun k => k+2) (hrot 2) (by change q 0 = 0; exact h.1)
      (by change q 1 = 0; exact h.2)
  · exact False.elim (pure_q_opposite_dihedral_nonintegral q hq
      (fun k => k+3) (hrot 3) (by change q 0 = 0; exact h.1)
      (by change q 2 = 0; exact h.2) hG)
  · exact qadjacent_dihedral_integral_named (fun _ => 0) q hpq hn hG rfl
      (fun k => k+1) (hrot 1) (by change q 3 = 0; exact h.2)
      (by change q 0 = 0; exact h.1)
  · exact qadjacent_dihedral_integral_named (fun _ => 0) q hpq hn hG rfl
      (fun k => k+3) (hrot 3) (by change q 1 = 0; exact h.1)
      (by change q 2 = 0; exact h.2)
  · exact False.elim (pure_q_opposite_nonintegral q hq h.1 h.2 hG)
  · exact qadjacent_integral_named q hpq hn hG h.1 h.2
#print axioms Paper7B4Analytic.pure_q_integral_named

theorem pure_q_integral_iff_named (q : Fin 4 → ℕ)
    (hq : 0 < ∑ k, q k) (hn : nOf 4 (fun _ => 0) q ≤ 49) :
    IsIntegralGraph (SG 4 (fun _ => 0) q) ↔
      Nonempty (SG 4 (fun _ => 0) q ≃g sunGraph 4 G20b) ∨
      Nonempty (SG 4 (fun _ => 0) q ≃g sunGraph 4 C42Ten) := by
  constructor
  · exact pure_q_integral_named q hq hn
  · intro h
    rcases h with he | he
    · exact Paper7Normalize.graphIso_integral _ _ (Classical.choice he).symm Paper7ControlB4.g20b_integral
    · exact Paper7Normalize.graphIso_integral _ _ (Classical.choice he).symm Paper7Control44.control_integral
#print axioms Paper7B4Analytic.pure_q_integral_iff_named

theorem original_pure_q_branch (L : Fin 4 → List ℕ)
    (hpend : 0 < pendantCount 4 L) (hn : order 4 L ≤ 49)
    (hG : IsIntegralGraph (sunGraph 4 L))
    (hpzero : Paper7Normalize.countP1 4 L = (fun _ => 0)) :
    Nonempty (sunGraph 4 L ≃g sunGraph 4 G20b) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 C42Ten) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 4 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 4 L
  let q := Paper7Normalize.countP2 4 L
  let e : sunGraph 4 L ≃g SG 4 p q := Paper7Normalize.sunNormalizeIso 4 L (by omega) hL
  have hcard := Fintype.card_congr e.toEquiv
  change order 4 L = order 4 (pq 4 p q) at hcard
  have hpos : 0 < pendantCount 4 (pq 4 p q) := by
    rw [Paper7CycleThree.order_eq_add_pendantCount,
      Paper7CycleThree.order_eq_add_pendantCount] at hcard
    omega
  have hpq : 0 < ∑ k, (p k+q k) :=
    (Paper7CycleThree.pq_pendants_positive 4 p q).mp hpos
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hn' : nOf 4 p q ≤ 49 := by rw [← Paper7Setup.sg_order,← hcard]; exact hn
  have hp' : p = (fun _ => 0) := hpzero
  have hclassified : Nonempty (SG 4 p q ≃g sunGraph 4 G20b) ∨
      Nonempty (SG 4 p q ≃g sunGraph 4 C42Ten) := by
    rw [hp'] at hpq hn' hI ⊢
    exact pure_q_integral_named q (by simpa using hpq) hn' hI
  rcases hclassified with hf | hf
  · exact Or.inl ⟨e.trans (Classical.choice hf)⟩
  · exact Or.inr ⟨e.trans (Classical.choice hf)⟩
#print axioms Paper7B4Analytic.original_pure_q_branch

theorem original_pure_q_integral_iff_named (L : Fin 4 → List ℕ)
    (hpend : 0 < pendantCount 4 L) (hn : order 4 L ≤ 49)
    (hpzero : Paper7Normalize.countP1 4 L = (fun _ => 0)) :
    IsIntegralGraph (sunGraph 4 L) ↔
      Nonempty (sunGraph 4 L ≃g sunGraph 4 G20b) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 C42Ten) := by
  constructor
  · intro hG
    exact original_pure_q_branch L hpend hn hG hpzero
  · intro h
    rcases h with he | he
    · exact Paper7Normalize.graphIso_integral _ _ (Classical.choice he).symm Paper7ControlB4.g20b_integral
    · exact Paper7Normalize.graphIso_integral _ _ (Classical.choice he).symm Paper7Control44.control_integral
#print axioms Paper7B4Analytic.original_pure_q_integral_iff_named

end Paper7B4Analytic
