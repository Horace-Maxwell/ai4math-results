import Research.Backfill.Paper7.B4OppositePParameters
import Research.Backfill.Paper7.B4MixedOppositeBranch

/-! Source-only complete opposite-P branch, with true G20a isomorphisms. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem opposite_p_complete_integral_iso_g20a (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : p 1 = 0) (hp2 : 0 < p 2) (hp3 : p 3 = 0)
    (hq : 0 < ∑ i, q i) (hn : nOf 4 p q ≤ 49) (hG : IsIntegralGraph (SG 4 p q)) :
    Nonempty (SG 4 p q ≃g sunGraph 4 G20a) := by
  obtain ⟨hq0,hq2⟩ := opposite_p_integral_q_disjoint p q hp0 hp1 hp2 hp3 hG
  have hpe : p = oppositeP (p 0) (p 2) := by
    funext i
    fin_cases i <;> simp [oppositeP,hp1,hp3]
  have hqe : q = oppositeQ (q 1) (q 3) := by
    funext i
    fin_cases i <;> simp [oppositeQ,hq0,hq2]
  have hqpos : 0 < q 1+q 3 := by
    simpa only [Fin.sum_univ_four,hq0,hq2,zero_add,add_zero] using hq
  have hn' : nOf 4 (oppositeP (p 0) (p 2)) (oppositeQ (q 1) (q 3)) ≤ 49 := by
    rw [← hpe,← hqe]
    exact hn
  have hG' : IsIntegralGraph (SG 4 (oppositeP (p 0) (p 2)) (oppositeQ (q 1) (q 3))) := by
    rw [← hpe,← hqe]
    exact hG
  obtain ⟨h0,h2⟩ := opposite_disjoint_integral_parameters (p 0) (p 2) (q 1) (q 3)
    hp0 hp2 hqpos hn' hG'
  have hrot : IsDihedral 4 (fun i : Fin 4 => i+1) := by
    refine ⟨1,Or.inl ?_⟩
    intro i
    fin_cases i <;> decide
  exact mixed_opposite_dihedral_integral_iso_g20a p q hG (fun i => i+1) hrot
    (by change p 1 = 0; exact hp1) (by change p 2 = 1; exact h2)
    (by change p 3 = 0; exact hp3) (by change p 0 = 1; exact h0)
    (by change q 2 = 0; exact hq2) (by change q 0 = 0; exact hq0)
#print axioms Paper7B4Analytic.opposite_p_complete_integral_iso_g20a

theorem opposite_p_complete_dihedral_iso_g20a (p q : Fin 4 → ℕ)
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (hp0 : 0 < p (σ 0)) (hp1 : p (σ 1) = 0)
    (hp2 : 0 < p (σ 2)) (hp3 : p (σ 3) = 0)
    (hq : 0 < ∑ i, q i) (hn : nOf 4 p q ≤ 49) (hG : IsIntegralGraph (SG 4 p q)) :
    Nonempty (SG 4 p q ≃g sunGraph 4 G20a) := by
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 p q (p ∘ σ) (q ∘ σ)
    (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hbij := Paper7PruningCanonical.dihedral_bijective 4 (by decide) σ hσ
  have hP : ∑ i, (p ∘ σ) i = ∑ i, p i := hbij.sum_comp p
  have hQ : ∑ i, (q ∘ σ) i = ∑ i, q i := hbij.sum_comp q
  have hq' : 0 < ∑ i, (q ∘ σ) i := by rw [hQ]; exact hq
  have hn' : nOf 4 (p ∘ σ) (q ∘ σ) ≤ 49 := by
    simpa only [nOf,hP,hQ] using hn
  obtain ⟨f⟩ := opposite_p_complete_integral_iso_g20a (p ∘ σ) (q ∘ σ)
    hp0 hp1 hp2 hp3 hq' hn' hI
  exact ⟨e.trans f⟩
#print axioms Paper7B4Analytic.opposite_p_complete_dihedral_iso_g20a

theorem original_opposite_p_complete_branch (L : Fin 4 → List ℕ)
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (hp0 : 0 < Paper7Normalize.countP1 4 L (σ 0))
    (hp1 : Paper7Normalize.countP1 4 L (σ 1) = 0)
    (hp2 : 0 < Paper7Normalize.countP1 4 L (σ 2))
    (hp3 : Paper7Normalize.countP1 4 L (σ 3) = 0)
    (hq : 0 < ∑ i, Paper7Normalize.countP2 4 L i)
    (hn : order 4 L ≤ 49) (hG : IsIntegralGraph (sunGraph 4 L)) :
    Nonempty (sunGraph 4 L ≃g sunGraph 4 G20a) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 4 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 4 L
  let q := Paper7Normalize.countP2 4 L
  let e : sunGraph 4 L ≃g SG 4 p q := Paper7Normalize.sunNormalizeIso 4 L (by omega) hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hc := Fintype.card_congr e.toEquiv
  change order 4 L = order 4 (pq 4 p q) at hc
  rw [Paper7Setup.sg_order] at hc
  have hn' : nOf 4 p q ≤ 49 := by omega
  obtain ⟨f⟩ := opposite_p_complete_dihedral_iso_g20a p q σ hσ hp0 hp1 hp2 hp3 hq hn' hI
  exact ⟨e.trans f⟩
#print axioms Paper7B4Analytic.original_opposite_p_complete_branch

end Paper7B4Analytic
