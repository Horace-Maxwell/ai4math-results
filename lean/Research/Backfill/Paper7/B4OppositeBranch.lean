import Research.Backfill.Paper7.B4OppositeClassification
import Research.Backfill.Paper7.ControlB4CertifiedReduction

/-! NEW SOURCE ONLY. Transport of the complete opposite-support branch back
to arbitrary original arm lists. The additional hypotheses select this branch
explicitly; no theorem here claims the complete ControlB4N49 proposition. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Matrix Classical

theorem opposite_dihedral_integral_iso_g13 (p q : Fin 4 → ℕ)
    (hp : 0 < ∑ k, (p k+q k)) (hG : IsIntegralGraph (SG 4 p q))
    (hq : q=(fun _ => 0))
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (h1 : (p ∘ σ) 1=0) (h3 : (p ∘ σ) 3=0) :
    Nonempty (SG 4 p q ≃g sunGraph 4 G13) := by
  subst q
  have hi := Paper7Setup.sg_iso_of_dihedral 4 p (fun _ => 0)
    (p ∘ σ) (fun _ => 0) (by decide) σ hσ rfl rfl
  let e : SG 4 p (fun _ => 0) ≃g SG 4 (p ∘ σ) (fun _ => 0) := Classical.choice hi
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hsum : ∑ k, (p ∘ σ) k=∑ k, p k :=
    (Paper7PruningCanonical.dihedral_bijective 4 (by decide) σ hσ).sum_comp p
  have hp' : 0 < ∑ k, ((p ∘ σ) k+(0 : ℕ)) := by
    simpa only [Nat.add_zero,hsum] using hp
  let f : SG 4 (p ∘ σ) (fun _ => 0) ≃g sunGraph 4 G13 :=
    Classical.choice (opposite_integral_iso_g13 (p ∘ σ) hp' hI h1 h3)
  exact ⟨e.trans f⟩
#print axioms Paper7B4Analytic.opposite_dihedral_integral_iso_g13

theorem original_opposite_branch (L : Fin 4 → List ℕ)
    (hpend : 0 < pendantCount 4 L) (_hn : order 4 L ≤ 49)
    (hG : IsIntegralGraph (sunGraph 4 L))
    (hq : Paper7Normalize.countP2 4 L=(fun _ => 0))
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (h1 : (Paper7Normalize.countP1 4 L ∘ σ) 1=0)
    (h3 : (Paper7Normalize.countP1 4 L ∘ σ) 3=0) :
    Nonempty (sunGraph 4 L ≃g sunGraph 4 G13) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 4 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 4 L
  let q := Paper7Normalize.countP2 4 L
  let e : sunGraph 4 L ≃g SG 4 p q :=
    Paper7Normalize.sunNormalizeIso 4 L (by omega) hL
  have hcard := Fintype.card_congr e.toEquiv
  change order 4 L=order 4 (pq 4 p q) at hcard
  have hpos : 0 < pendantCount 4 (pq 4 p q) := by
    rw [Paper7CycleThree.order_eq_add_pendantCount,
      Paper7CycleThree.order_eq_add_pendantCount] at hcard
    omega
  have hp : 0 < ∑ k, (p k+q k) :=
    (Paper7CycleThree.pq_pendants_positive 4 p q).mp hpos
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hf := opposite_dihedral_integral_iso_g13 p q hp hI hq σ hσ h1 h3
  let f : SG 4 p q ≃g sunGraph 4 G13 := Classical.choice hf
  exact ⟨e.trans f⟩
#print axioms Paper7B4Analytic.original_opposite_branch

end Paper7B4Analytic
