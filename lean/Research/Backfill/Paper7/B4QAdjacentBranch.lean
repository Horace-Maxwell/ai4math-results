import Research.Backfill.Paper7.B4QAdjacentClassification
import Research.Backfill.Paper7.ControlB4CertifiedReduction

/-! SOURCE ONLY. Dihedral and original-arm-list transport for the complete
adjacent-q branch. Its explicit support conditions select a proper subbranch
of ControlB4N49. No full ControlB4N49 check is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Matrix Classical

theorem qadjacent_dihedral_integral_named (p q : Fin 4 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 4 p q ≤ 49)
    (hG : IsIntegralGraph (SG 4 p q)) (hpzero : p = (fun _ => 0))
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (h2 : (q ∘ σ) 2 = 0) (h3 : (q ∘ σ) 3 = 0) :
    Nonempty (SG 4 p q ≃g sunGraph 4 G20b) ∨
      Nonempty (SG 4 p q ≃g sunGraph 4 C42Ten) := by
  subst p
  have hi := Paper7Setup.sg_iso_of_dihedral 4 (fun _ => 0) q
    (fun _ => 0) (q ∘ σ) (by decide) σ hσ rfl rfl
  let e : SG 4 (fun _ => 0) q ≃g SG 4 (fun _ => 0) (q ∘ σ) := Classical.choice hi
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hsum : ∑ k, (q ∘ σ) k = ∑ k, q k :=
    (Paper7PruningCanonical.dihedral_bijective 4 (by decide) σ hσ).sum_comp q
  have hp' : 0 < ∑ k, ((0 : ℕ) + (q ∘ σ) k) := by
    simpa only [Nat.zero_add, hsum] using hp
  have hn' : nOf 4 (fun _ => 0) (q ∘ σ) ≤ 49 := by
    simpa only [nOf, hsum] using hn
  rcases qadjacent_integral_named (q ∘ σ) hp' hn' hI h2 h3 with hg | hc
  · let f : SG 4 (fun _ => 0) (q ∘ σ) ≃g sunGraph 4 G20b := Classical.choice hg
    exact Or.inl ⟨e.trans f⟩
  · let f : SG 4 (fun _ => 0) (q ∘ σ) ≃g sunGraph 4 C42Ten := Classical.choice hc
    exact Or.inr ⟨e.trans f⟩
#print axioms Paper7B4Analytic.qadjacent_dihedral_integral_named

theorem original_qadjacent_branch (L : Fin 4 → List ℕ)
    (hpend : 0 < pendantCount 4 L) (hn : order 4 L ≤ 49)
    (hG : IsIntegralGraph (sunGraph 4 L))
    (hpzero : Paper7Normalize.countP1 4 L = (fun _ => 0))
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (h2 : (Paper7Normalize.countP2 4 L ∘ σ) 2 = 0)
    (h3 : (Paper7Normalize.countP2 4 L ∘ σ) 3 = 0) :
    Nonempty (sunGraph 4 L ≃g sunGraph 4 G20b) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 C42Ten) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 4 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j, rfl⟩)
  let p := Paper7Normalize.countP1 4 L
  let q := Paper7Normalize.countP2 4 L
  let e : sunGraph 4 L ≃g SG 4 p q :=
    Paper7Normalize.sunNormalizeIso 4 L (by omega) hL
  have hcard := Fintype.card_congr e.toEquiv
  change order 4 L = order 4 (pq 4 p q) at hcard
  have hsize : order 4 L = nOf 4 p q := hcard.trans (Paper7Setup.sg_order 4 p q)
  have hn' : nOf 4 p q ≤ 49 := by omega
  have hpos : 0 < pendantCount 4 (pq 4 p q) := by
    rw [Paper7CycleThree.order_eq_add_pendantCount,
      Paper7CycleThree.order_eq_add_pendantCount] at hcard
    omega
  have hp : 0 < ∑ k, (p k + q k) :=
    (Paper7CycleThree.pq_pendants_positive 4 p q).mp hpos
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  rcases qadjacent_dihedral_integral_named p q hp hn' hI hpzero σ hσ h2 h3 with hg | hc
  · let f : SG 4 p q ≃g sunGraph 4 G20b := Classical.choice hg
    exact Or.inl ⟨e.trans f⟩
  · let f : SG 4 p q ≃g sunGraph 4 C42Ten := Classical.choice hc
    exact Or.inr ⟨e.trans f⟩
#print axioms Paper7B4Analytic.original_qadjacent_branch

end Paper7B4Analytic
