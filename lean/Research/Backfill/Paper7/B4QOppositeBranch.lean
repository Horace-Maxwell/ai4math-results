import Research.Backfill.Paper7.B4QOppositeExclusion
import Research.Backfill.Paper7.ControlB4CertifiedReduction

/-! Source-only transport of the complete pure-q opposite-support exclusion.
The original arm lists are normalized using the accepted integral-graph theorem. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem pure_q_opposite_dihedral_nonintegral (q : Fin 4 → ℕ)
    (hq : 0 < ∑ k, q k) (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (h1 : (q ∘ σ) 1 = 0) (h3 : (q ∘ σ) 3 = 0) :
    ¬ IsIntegralGraph (SG 4 (fun _ => 0) q) := by
  intro hG
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 (fun _ => 0) q
    (fun _ => 0) (q ∘ σ) (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hsum : ∑ k, (q ∘ σ) k = ∑ k, q k :=
    (Paper7PruningCanonical.dihedral_bijective 4 (by decide) σ hσ).sum_comp q
  have hq' : 0 < ∑ k, (q ∘ σ) k := by rw [hsum]; exact hq
  exact pure_q_opposite_nonintegral (q ∘ σ) hq' h1 h3 hI
#print axioms Paper7B4Analytic.pure_q_opposite_dihedral_nonintegral

theorem original_pure_q_opposite_nonintegral (L : Fin 4 → List ℕ)
    (hpend : 0 < pendantCount 4 L)
    (hpzero : Paper7Normalize.countP1 4 L = (fun _ => 0))
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (h1 : (Paper7Normalize.countP2 4 L ∘ σ) 1 = 0)
    (h3 : (Paper7Normalize.countP2 4 L ∘ σ) 3 = 0) :
    ¬ IsIntegralGraph (sunGraph 4 L) := by
  intro hG
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
  have hp' : p = (fun _ => 0) := hpzero
  rw [hp'] at hpq hI
  have hq : 0 < ∑ k, q k := by simpa only [Nat.zero_add] using hpq
  exact pure_q_opposite_dihedral_nonintegral q hq σ hσ h1 h3 hI
#print axioms Paper7B4Analytic.original_pure_q_opposite_nonintegral

end Paper7B4Analytic
