import Research.Backfill.Paper7.SunPQNormalization
import Research.Backfill.Paper7.GraphIsoIntegral
import Research.Backfill.Paper7.SetupCardinality
import Research.Backfill.Paper7.BMSTheorem21Complete

/-! Arbitrary lists, including zero-length arms, reduce to the original P1/P2
parameters through an actual graph isomorphism. No finite exclusion is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open BackfillPaper7.Challenge Paper7Normalize
open scoped BigOperators Classical

theorem order_eq_add_pendantCount (b : ℕ) (L : Fin b → List ℕ) :
    order b L = b + pendantCount b L := by
  change Fintype.card (SunV b L) = b + ∑ k, (L k).sum
  simp only [SunV, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  change (∑ j : Fin (L k).length, (L k)[j.val]) = (L k).sum
  exact Fin.sum_univ_getElem (L k)
#print axioms Paper7CycleThree.order_eq_add_pendantCount

theorem pq_pendantCount (b : ℕ) (p q : Fin b → ℕ) :
    pendantCount b (pq b p q) = ∑ k, p k + 2 * ∑ k, q k := by
  simp [pendantCount, pq, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]
#print axioms Paper7CycleThree.pq_pendantCount

theorem pq_pendants_positive (b : ℕ) (p q : Fin b → ℕ) :
    0 < pendantCount b (pq b p q) ↔ 0 < ∑ k, (p k + q k) := by
  rw [pq_pendantCount, Finset.sum_add_distrib]
  omega
#print axioms Paper7CycleThree.pq_pendants_positive

theorem integral_normalization (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (hp : 0 < pendantCount b L) (hG : IsIntegralGraph (sunGraph b L)) :
    ∃ p q : Fin b → ℕ, IsIntegralGraph (SG b p q) ∧
      order b L = nOf b p q ∧ 0 < ∑ k, (p k + q k) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 b L hb hG k _ (List.mem_iff_get.mpr ⟨j, rfl⟩)
  let p := countP1 b L
  let q := countP2 b L
  have hI : IsIntegralGraph (SG b p q) :=
    graphIso_integral (sunGraph b L) (SG b p q) (sunNormalizeIso b L hb hL) hG
  have hcard := Fintype.card_congr (sunNormalizeIso b L hb hL).toEquiv
  change order b L = order b (pq b p q) at hcard
  have hn : order b L = nOf b p q := hcard.trans (Paper7Setup.sg_order b p q)
  refine ⟨p, q, hI, hn, ?_⟩
  have hpos : 0 < pendantCount b (pq b p q) := by
    rw [order_eq_add_pendantCount, order_eq_add_pendantCount] at hcard
    omega
  exact (pq_pendants_positive b p q).mp hpos
#print axioms Paper7CycleThree.integral_normalization

theorem triangle_parameter_bounds (p q : Fin 3 → ℕ) (hn : nOf 3 p q ≤ 49) :
    (∀ k, p k ≤ 46) ∧ (∀ k, q k ≤ 23) := by
  have hp (k : Fin 3) : p k ≤ ∑ i, p i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hq (k : Fin 3) : q k ≤ ∑ i, q i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  unfold nOf at hn
  constructor
  · intro k
    have := hp k
    omega
  · intro k
    have := hq k
    omega
#print axioms Paper7CycleThree.triangle_parameter_bounds

/-- Exact reduction of the frozen contract. This is an equivalence, not a proof
of its right-hand side and not the final `check_Section6CycleThree`. -/
theorem section6_cycle_three_iff_bounded_pq : Section6CycleThree ↔
    ∀ p q : Fin 3 → ℕ, 0 < ∑ k, (p k + q k) → nOf 3 p q ≤ 49 →
      ¬ IsIntegralGraph (SG 3 p q) := by
  constructor
  · intro h p q hp hn hG
    have h50 := h (pq 3 p q) ((pq_pendants_positive 3 p q).mpr hp) hG
    rw [Paper7Setup.sg_order] at h50
    omega
  · intro h L hp hG
    obtain ⟨p, q, hI, hn, hpos⟩ := integral_normalization 3 L (by omega) hp hG
    by_contra hsmall
    have h49 : nOf 3 p q ≤ 49 := by omega
    exact h p q hpos h49 hI
#print axioms Paper7CycleThree.section6_cycle_three_iff_bounded_pq

end Paper7CycleThree
