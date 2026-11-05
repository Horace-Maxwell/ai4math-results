import Research.Backfill.Paper7.ControlB4Representatives
import Research.Backfill.Paper7.CycleThreeReduction
import Research.Backfill.Paper7.IntegralLeafCompleteness

/-! Arbitrary original arm lists, including zero-length arms, reduce to actual
certified outputs in the unchanged b=4,N=49 domain. No classification assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7ControlB4
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7Normalize Paper7CycleThree Paper7PruningCanonical Paper7PruningGuards
open scoped BigOperators

theorem b4_runDomain : RunDomain (.a6 true) 4 49 := by
  norm_num [RunDomain]
#print axioms Paper7ControlB4.b4_runDomain

theorem b4_integral_normalization (L : Fin 4 → List ℕ)
    (hpend : 0 < pendantCount 4 L) (hn : order 4 L ≤ 49)
    (hG : IsIntegralGraph (sunGraph 4 L)) :
    ∃ x : PQ 4, Budget 4 49 x ∧ IsIntegralGraph (SG 4 x.1 x.2) ∧
      Nonempty (sunGraph 4 L ≃g SG 4 x.1 x.2) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 4 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j, rfl⟩)
  let p := countP1 4 L
  let q := countP2 4 L
  let e : sunGraph 4 L ≃g SG 4 p q := sunNormalizeIso 4 L (by omega) hL
  have hcard := Fintype.card_congr e.toEquiv
  change order 4 L = order 4 (pq 4 p q) at hcard
  have hsize : order 4 L = nOf 4 p q := hcard.trans (Paper7Setup.sg_order 4 p q)
  have hpos : 0 < pendantCount 4 (pq 4 p q) := by
    rw [order_eq_add_pendantCount, order_eq_add_pendantCount] at hcard
    omega
  have hweight : pendantCount 4 (pq 4 p q) = weight (p, q) := by
    exact pq_pendantCount 4 p q
  have hbudget : Budget 4 49 (p, q) := by
    constructor
    · rwa [← hweight]
    · have hh : nOf 4 p q ≤ 49 := by omega
      simpa only [nOf, weight, pSum, qSum, Nat.add_assoc] using hh
  exact ⟨(p, q), hbudget, graphIso_integral _ _ e hG, ⟨e⟩⟩
#print axioms Paper7ControlB4.b4_integral_normalization

theorem b4_certified_budget (x : PQ 4) (hx : x ∈ CertifiedOutputs (.a6 true) 4 49) :
    Budget 4 49 x := by
  have hleaf := ((Paper7Pruning.certifiedOutputs_iff (.a6 true) 4 49 x).mp hx).1
  have he := hleaf.1
  rw [Paper7Pruning.enumerated_eq_budget 4 49 (by omega)] at he
  exact he
#print axioms Paper7ControlB4.b4_certified_budget

/-- The certified set is mathematical: all original guards and the genuine
integrality test are retained. Membership is not inferred from a legacy log. -/
theorem b4_integral_iff_certified_iso (L : Fin 4 → List ℕ)
    (hpend : 0 < pendantCount 4 L) (hn : order 4 L ≤ 49) :
    IsIntegralGraph (sunGraph 4 L) ↔
      ∃ y : PQ 4, y ∈ CertifiedOutputs (.a6 true) 4 49 ∧
        Nonempty (sunGraph 4 L ≃g SG 4 y.1 y.2) := by
  constructor
  · intro hG
    obtain ⟨x, hx, hI, ⟨e⟩⟩ := b4_integral_normalization L hpend hn hG
    obtain ⟨σ, hσ, hcert⟩ :=
      (integral_iff_certified_orbit (.a6 true) 4 49 b4_runDomain x hx).mp hI
    obtain ⟨f⟩ := reindex_sg_iso 4 (by omega) σ hσ x
    exact ⟨reindex σ x, hcert, ⟨e.trans f⟩⟩
  · rintro ⟨y, hy, ⟨e⟩⟩
    have hI := ((Paper7Pruning.certifiedOutputs_iff (.a6 true) 4 49 y).mp hy).2
    exact graphIso_integral _ _ e.symm hI
#print axioms Paper7ControlB4.b4_integral_iff_certified_iso

/-- Exact remaining classification obligation, deliberately only a definition. -/
def B4CertifiedFour : Prop :=
  ∀ y : PQ 4, y ∈ CertifiedOutputs (.a6 true) 4 49 → FourNamed (SG 4 y.1 y.2)
#print axioms Paper7ControlB4.B4CertifiedFour

/-- An equivalence with the original contract, not a proof of either side.
There is no extra finite-coverage premise on a purported final check. -/
theorem controlB4N49_iff_certified_four : ControlB4N49 ↔ B4CertifiedFour := by
  constructor
  · intro h y hy
    have hb := b4_certified_budget y hy
    have hpos : 0 < pendantCount 4 (pq 4 y.1 y.2) := by
      simpa only [pq_pendantCount, weight, pSum, qSum] using hb.1
    have hn : order 4 (pq 4 y.1 y.2) ≤ 49 := by
      rw [Paper7Setup.sg_order]
      simpa only [nOf, weight, pSum, qSum, Nat.add_assoc] using hb.2
    have hI := ((Paper7Pruning.certifiedOutputs_iff (.a6 true) 4 49 y).mp hy).2
    exact (h (pq 4 y.1 y.2) hpos hn).mp hI
  · intro h L hpend hn
    constructor
    · intro hI
      obtain ⟨y, hy, ⟨e⟩⟩ := (b4_integral_iff_certified_iso L hpend hn).mp hI
      exact (fourNamed_iso_iff _ _ e).mpr (h y hy)
    · exact control_b4_reverse L
#print axioms Paper7ControlB4.controlB4N49_iff_certified_four

end Paper7ControlB4
