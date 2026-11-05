import Research.Backfill.Paper7.SunPQNormalization
import Research.Backfill.Paper7.GraphIsoIntegral
import Research.Backfill.Paper7.BareCycleObstruction
import Research.Backfill.Paper7.Lemma44
import Research.Backfill.Paper7.BMSTheorem21Complete

/-! The exact frozen arbitrary-list contract. BMS imports remain pending
source candidates until Root records actual successful compilation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Paper7Normalize
open BackfillPaper7.Challenge

theorem normalized_order (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2) :
    order b L = nOf b (countP1 b L) (countP2 b L) := by
  have h := Fintype.card_congr (sunNormalizeIso b L hb hL).toEquiv
  change order b L = order b (pq b (countP1 b L) (countP2 b L)) at h
  exact h.trans (Paper7Setup.sg_order b (countP1 b L) (countP2 b L))
#print axioms Paper7Normalize.normalized_order

theorem check_Corollary43 : BackfillPaper7.Challenge.Corollary43 := by
  intro b L hb hG
  have hb3 : 3 ≤ b := by rcases hb with rfl | rfl <;> omega
  have hb7 : 7 ≤ b := by rcases hb with rfl | rfl <;> omega
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 b L hb3 hG k _ (List.mem_iff_get.mpr ⟨j, rfl⟩)
  let p : Fin b → ℕ := countP1 b L
  let q : Fin b → ℕ := countP2 b L
  have hI : IsIntegralGraph (SG b p q) :=
    graphIso_integral (sunGraph b L) (SG b p q) (sunNormalizeIso b L hb3 hL) hG
  have hsize : order b L = nOf b p q := normalized_order b L hb3 hL
  by_cases hpos : 0 < ∑ k, (p k + q k)
  · by_contra hsmall
    have hn : nOf b p q ≤ 42 := by rw [← hsize]; omega
    have h13 := (Paper7Rank.check_Lemma44 b p q hb3 hpos hI).2.2.2.2.2 hn
    rcases hb with rfl | rfl <;> omega
  · have hsum : ∑ k, (p k + q k) = 0 := Nat.eq_zero_of_not_pos hpos
    have hpoint (k : Fin b) : p k + q k = 0 := by
      have hle : p k + q k ≤ ∑ i, (p i + q i) :=
        Finset.single_le_sum (f := fun i : Fin b => p i + q i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      omega
    have hp : p = fun _ => 0 := by funext k; have := hpoint k; omega
    have hq : q = fun _ => 0 := by funext k; have := hpoint k; omega
    rw [hp, hq] at hI
    exact False.elim (bare_cycle_not_integral b hb7 hI)
#print axioms Paper7Normalize.check_Corollary43

end Paper7Normalize
