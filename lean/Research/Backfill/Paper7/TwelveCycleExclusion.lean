import Research.Backfill.Paper7.TwelveCycleTransfer
import Research.Backfill.Paper7.CycleThreeReduction
import Research.Backfill.Paper7.DihedralOrbitBasics

/-! Source-only full twelve-cycle exclusion in the original order domain.
The P₂ exclusion, support parity and unit monodromy are all proved inputs. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MainReduction
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem twelve_qzero_nonintegral (p : Fin 12 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 12 p (fun _ => 0) ≤ 42) : ¬ IsIntegralGraph (SG 12 p (fun _ => 0)) := by
  intro hG
  obtain ⟨_hc,_hm,hd⟩ := twelve_qzero_unit_rank p hp hn hG
  obtain ⟨k,hk⟩ : ∃ k : Fin 12, 0 < p k := by
    by_contra hh
    push Not at hh
    have hz : ∑ k, p k = 0 := Finset.sum_eq_zero (fun i _ => by have hi := hh i; omega)
    omega
  let σ : Fin 12 → Fin 12 := fun i => i+k
  have hσ : IsDihedral 12 σ := by
    refine ⟨k,Or.inl ?_⟩
    intro i
    rfl
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 12 p (fun _ => 0)
    (p ∘ σ) (fun _ => 0) (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hsum : ∑ i, (p ∘ σ) i = ∑ i, p i :=
    (Paper7PruningCanonical.dihedral_bijective 12 (by decide) σ hσ).sum_comp p
  have hp' : 0 < ∑ i, (p ∘ σ) i := by rw [hsum]; exact hp
  have hn' : nOf 12 (p ∘ σ) (fun _ => 0) ≤ 42 := by
    simpa only [nOf,hsum] using hn
  obtain ⟨_hc',hm',_hd'⟩ := twelve_qzero_unit_rank (p ∘ σ) hp' hn' hI
  have hid := qzero_unit_transfer_identity 12 (p ∘ σ) (by decide) hm'
  obtain ⟨h1,h3,h5,h7,h9,h11⟩ := twelve_saturated_rotated_odd_zero p hd k hk
  have hz := twelve_alternating_unit_identity_zero (p ∘ σ) h1 h3 h5 h7 h9 h11 hid
  have hz' : p k = 0 := by simpa [σ] using hz
  omega
#print axioms Paper7MainReduction.twelve_qzero_nonintegral

theorem twelve_parameters_nonintegral (p q : Fin 12 → ℕ)
    (hp : 0 < ∑ i, (p i+q i)) (hn : nOf 12 p q ≤ 42) : ¬ IsIntegralGraph (SG 12 p q) := by
  intro hG
  have hq := twelve_or_larger_cycle_qzero 12 p q (by decide) hn hG
  rw [hq] at hp hn hG
  exact twelve_qzero_nonintegral p (by simpa using hp) hn hG
#print axioms Paper7MainReduction.twelve_parameters_nonintegral

theorem original_twelve_order_gt_forty_two (L : Fin 12 → List ℕ)
    (hp : 0 < pendantCount 12 L) (hG : IsIntegralGraph (sunGraph 12 L)) :
    42 < order 12 L := by
  by_contra hn
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 12 L (by decide) hG k _ (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 12 L
  let q := Paper7Normalize.countP2 12 L
  let e : sunGraph 12 L ≃g SG 12 p q := Paper7Normalize.sunNormalizeIso 12 L (by decide) hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hc := Fintype.card_congr e.toEquiv
  change order 12 L = order 12 (pq 12 p q) at hc
  have hpq : 0 < pendantCount 12 (pq 12 p q) := by
    rw [Paper7CycleThree.order_eq_add_pendantCount,
      Paper7CycleThree.order_eq_add_pendantCount] at hc
    omega
  have hpos := (Paper7CycleThree.pq_pendants_positive 12 p q).mp hpq
  rw [Paper7Setup.sg_order] at hc
  exact twelve_parameters_nonintegral p q hpos (by omega) hI
#print axioms Paper7MainReduction.original_twelve_order_gt_forty_two

end Paper7MainReduction
