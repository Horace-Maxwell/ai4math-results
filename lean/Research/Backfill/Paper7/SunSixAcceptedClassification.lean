import Research.Backfill.Paper7.C61AnalyticOrbitClassification
import Research.Backfill.Paper7.CycleThreeReduction

/-! NEW SOURCE ONLY. The accepted C61OrbitSix contract is transported back to
arbitrary original lists, including zero-length entries, by an actual graph
isomorphism. There is no finite-search premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleLength
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem c61_parameter_order : nOf 6 C61P (fun _ => 0) = 42 := by
  norm_num [nOf, C61P, Fin.sum_univ_six]
#print axioms Paper7CycleLength.c61_parameter_order

theorem c61_counterexample_with_order : IsCounterexample 6 C61 ∧ order 6 C61 = 42 := by
  have hn : order 6 C61 = 42 := by
    rw [Paper7C61Analytic.check_C61OrbitSix.1, Paper7Setup.sg_order]
    exact c61_parameter_order
  have hp : 0 < pendantCount 6 C61 := by
    have hsize := Paper7CycleThree.order_eq_add_pendantCount 6 C61
    omega
  have hG : IsIntegralGraph (sunGraph 6 C61) := by
    rw [Paper7C61Analytic.check_C61OrbitSix.1]
    exact Paper7C61Classification.c61_integral
  exact ⟨⟨by omega, hp, hG, by norm_num⟩, hn⟩
#print axioms Paper7CycleLength.c61_counterexample_with_order

theorem integral_six_parameters_order (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) : nOf 6 p q = 42 := by
  obtain ⟨hq, hpRot⟩ :=
    (Paper7C61Analytic.check_C61OrbitSix.2.2.2 p q hp hn).mp hG
  obtain ⟨σ, hσ, hpσ⟩ :=
    (Paper7C61Analytic.check_C61OrbitSix.2.1 p).mpr hpRot
  calc
    nOf 6 p q = nOf 6 (C61P ∘ σ) ((fun _ => 0) ∘ σ) := by
      rw [hq, hpσ]
      rfl
    _ = nOf 6 C61P (fun _ => 0) :=
      Paper7C61Classification.nOf_comp C61P (fun _ => 0) σ hσ
    _ = 42 := c61_parameter_order
#print axioms Paper7CycleLength.integral_six_parameters_order

theorem integral_six_parameters_iso (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) :
    Nonempty (SG 6 p q ≃g sunGraph 6 C61) := by
  obtain ⟨hq, hpRot⟩ :=
    (Paper7C61Analytic.check_C61OrbitSix.2.2.2 p q hp hn).mp hG
  obtain ⟨σ, hσ, hpσ⟩ :=
    (Paper7C61Analytic.check_C61OrbitSix.2.1 p).mpr hpRot
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 6 C61P (fun _ => 0) p q
    (by omega) σ hσ hpσ (by simpa only [Function.comp_def] using hq)
  rw [Paper7C61Analytic.check_C61OrbitSix.1]
  exact ⟨e.symm⟩
#print axioms Paper7CycleLength.integral_six_parameters_iso

theorem original_integral_six_order (L : Fin 6 → List ℕ)
    (hp : 0 < pendantCount 6 L) (hG : IsIntegralGraph (sunGraph 6 L))
    (hn : order 6 L ≤ 42) : order 6 L = 42 := by
  obtain ⟨p, q, hI, hsize, hpos⟩ :=
    Paper7CycleThree.integral_normalization 6 L (by omega) hp hG
  have hn' : nOf 6 p q ≤ 42 := by omega
  exact hsize.trans (integral_six_parameters_order p q hpos hn' hI)
#print axioms Paper7CycleLength.original_integral_six_order

theorem original_integral_six_iso (L : Fin 6 → List ℕ)
    (hp : 0 < pendantCount 6 L) (hG : IsIntegralGraph (sunGraph 6 L))
    (hn : order 6 L ≤ 42) : Nonempty (sunGraph 6 L ≃g sunGraph 6 C61) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 6 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j, rfl⟩)
  let p := Paper7Normalize.countP1 6 L
  let q := Paper7Normalize.countP2 6 L
  let e : sunGraph 6 L ≃g SG 6 p q :=
    Paper7Normalize.sunNormalizeIso 6 L (by omega) hL
  have hI : IsIntegralGraph (SG 6 p q) :=
    Paper7Normalize.graphIso_integral _ _ e hG
  have hcard := Fintype.card_congr e.toEquiv
  change order 6 L = order 6 (pq 6 p q) at hcard
  have hsize : order 6 L = nOf 6 p q :=
    hcard.trans (Paper7Setup.sg_order 6 p q)
  have hpos : 0 < pendantCount 6 (pq 6 p q) := by
    rw [Paper7CycleThree.order_eq_add_pendantCount,
      Paper7CycleThree.order_eq_add_pendantCount] at hcard
    omega
  have hpq := (Paper7CycleThree.pq_pendants_positive 6 p q).mp hpos
  obtain ⟨f⟩ := integral_six_parameters_iso p q hpq (by omega) hI
  exact ⟨e.trans f⟩
#print axioms Paper7CycleLength.original_integral_six_iso

end Paper7CycleLength
