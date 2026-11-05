import Research.Backfill.Paper7.B4ThreePExclusion
import Research.Backfill.Paper7.B4QzeroFourExclusion
import Research.Backfill.Paper7.B4AdjacentZeroExclusion

/-! Source-only complete q=0 branch of the original four-cycle classification.
All support sizes are proved; no support coverage premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem qzero_integral_iso_g13 (p : Fin 4 → ℕ)
    (hp : 0 < ∑ k, p k) (hn : nOf 4 p (fun _ => 0) ≤ 49)
    (hG : IsIntegralGraph (SG 4 p (fun _ => 0))) :
    Nonempty (SG 4 p (fun _ => 0) ≃g sunGraph 4 G13) := by
  by_cases hfull : ∀ i, 0 < p i
  · exact False.elim (qzero_four_positive_nonintegral p hfull hn hG)
  obtain ⟨i,hi⟩ : ∃ i : Fin 4, p i = 0 := by
    push Not at hfull
    obtain ⟨i,hi⟩ := hfull
    exact ⟨i,by omega⟩
  by_cases htwo : ∃ j : Fin 4, j ≠ i ∧ p j = 0
  · obtain ⟨j,hji,hj⟩ := htwo
    exact qzero_two_zero_sites_iso_g13 p (by simpa using hp) hG i j (Ne.symm hji) hi hj
  have hpos : ∀ j : Fin 4, j ≠ i → 0 < p j := by
    intro j hji
    by_contra hh
    exact htwo ⟨j,hji,by omega⟩
  let σ : Fin 4 → Fin 4 := fun k => k+(i+1)
  have hσ : IsDihedral 4 σ := by
    refine ⟨i+1,Or.inl ?_⟩
    intro k
    fin_cases i <;> fin_cases k <;> decide
  have h0 : 0 < (p ∘ σ) 0 := by
    apply hpos
    fin_cases i <;> decide
  have h1 : 0 < (p ∘ σ) 1 := by
    apply hpos
    fin_cases i <;> decide
  have h2 : 0 < (p ∘ σ) 2 := by
    apply hpos
    fin_cases i <;> decide
  have h3 : (p ∘ σ) 3 = 0 := by
    have hindex : σ 3 = i := by fin_cases i <;> rfl
    change p (σ 3) = 0
    rw [hindex]
    exact hi
  exact False.elim (three_positive_dihedral_nonintegral p hn σ hσ h0 h1 h2 h3 hG)
#print axioms Paper7B4Analytic.qzero_integral_iso_g13

theorem qzero_integral_iff_iso_g13 (p : Fin 4 → ℕ)
    (hp : 0 < ∑ k, p k) (hn : nOf 4 p (fun _ => 0) ≤ 49) :
    IsIntegralGraph (SG 4 p (fun _ => 0)) ↔
      Nonempty (SG 4 p (fun _ => 0) ≃g sunGraph 4 G13) := by
  constructor
  · exact qzero_integral_iso_g13 p hp hn
  · rintro ⟨e⟩
    exact Paper7Normalize.graphIso_integral _ _ e.symm Paper7ControlB4.g13_integral
#print axioms Paper7B4Analytic.qzero_integral_iff_iso_g13

theorem original_qzero_branch (L : Fin 4 → List ℕ)
    (hpend : 0 < pendantCount 4 L) (hn : order 4 L ≤ 49)
    (hG : IsIntegralGraph (sunGraph 4 L))
    (hq : Paper7Normalize.countP2 4 L = (fun _ => 0)) :
    Nonempty (sunGraph 4 L ≃g sunGraph 4 G13) := by
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
  have hp : 0 < ∑ k, (p k+q k) :=
    (Paper7CycleThree.pq_pendants_positive 4 p q).mp hpos
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hn' : nOf 4 p q ≤ 49 := by rw [← Paper7Setup.sg_order,← hcard]; exact hn
  have hq' : q = (fun _ => 0) := hq
  have hclassified : Nonempty (SG 4 p q ≃g sunGraph 4 G13) := by
    rw [hq'] at hp hn' hI ⊢
    apply qzero_integral_iso_g13 p (by simpa using hp) hn' hI
  obtain ⟨f⟩ := hclassified
  exact ⟨e.trans f⟩
#print axioms Paper7B4Analytic.original_qzero_branch

theorem original_qzero_integral_iff_g13 (L : Fin 4 → List ℕ)
    (hpend : 0 < pendantCount 4 L) (hn : order 4 L ≤ 49)
    (hq : Paper7Normalize.countP2 4 L = (fun _ => 0)) :
    IsIntegralGraph (sunGraph 4 L) ↔ Nonempty (sunGraph 4 L ≃g sunGraph 4 G13) := by
  constructor
  · intro hG
    exact original_qzero_branch L hpend hn hG hq
  · rintro ⟨e⟩
    exact Paper7Normalize.graphIso_integral _ _ e.symm Paper7ControlB4.g13_integral
#print axioms Paper7B4Analytic.original_qzero_integral_iff_g13

end Paper7B4Analytic
