import Research.Backfill.Paper5.Proof.DiagramUnits
import Research.Backfill.Paper5.Proof.DiagramExtraction

set_option autoImplicit false

namespace CodexPaper5.DiagramRank

open BackfillPaper5 Function

/-- A point fixed by both actual generators has a singleton moving-edge component.
No finiteness hypothesis is needed. -/
theorem reachable_eq_of_common_fixed {V : Type*} (α β : Equiv.Perm V)
    (hα : Involutive α) (hβ : Involutive β) {a b : V}
    (ha : α a = a) (hb : β a = a)
    (hr : (InvolutionEndpoints.movingGraph α β).Reachable a b) : b = a := by
  obtain ⟨k, hk⟩ := InvolutionEndpoints.sameCycle_of_reachable α β hα hβ ha hr
  have hfixed : (α * β) a = a := by
    change α (β a) = a
    rw [hb, ha]
  exact hk.symm.trans (Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfixed k)

/-- A horizontal top block of the left factor remains exactly that block in the product,
including the singleton case. The product is the frozen list search. -/
theorem dmul_inl_eq_of_inl {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) {a b : Fin n}
    (hxa : x (Sum.inl a) = Sum.inl b) :
    Challenge.dmul x y (Sum.inl a) = Sum.inl b := by
  by_cases hba : b = a
  · subst b
    apply DiagramProduct.dmul_eq_self_of_no_partner x y (Sum.inl a)
    intro q hq hreach
    rw [StackGeometry.stackGraph_eq_movingGraph hx hy] at hreach
    have hupper : StackGeometry.upperPerm hx (Challenge.outer (Sum.inl a)) =
        Challenge.outer (Sum.inl a) := by
      change StackGeometry.upperMap x (Challenge.upper (Sum.inl a)) =
        Challenge.upper (Sum.inl a)
      rw [StackGeometry.upperMap_upper, hxa]
    have hlower : StackGeometry.lowerPerm hy (Challenge.outer (Sum.inl a)) =
        Challenge.outer (Sum.inl a) := rfl
    have heq := reachable_eq_of_common_fixed (StackGeometry.upperPerm hx)
      (StackGeometry.lowerPerm hy) (StackGeometry.upperMap_involutive hx)
      (StackGeometry.lowerMap_involutive hy) hupper hlower hreach
    exact hq (StackGeometry.outer_injective heq)
  · have hne : (Sum.inl b : Challenge.Pt n) ≠ Sum.inl a :=
      fun h => hba (Sum.inl.inj h)
    have hreach : (Challenge.stackGraph x y).Reachable
        (Challenge.outer (Sum.inl a)) (Challenge.outer (Sum.inl b)) := by
      apply DiagramUnits.reachable_of_stackEdge x y
      exact Or.inl ⟨Sum.inl a, rfl, by simp only [hxa, Challenge.upper, Challenge.outer]⟩
    apply DiagramProduct.dmul_eq_of_partner x y (Sum.inl a) (Sum.inl b) hne hreach
    intro q hq hpath
    exact StackGeometry.outer_partner_unique hx hy hq hne hpath hreach

/-- A horizontal bottom block of the right factor remains exactly that block in the product,
including the singleton case. This uses the actual lower factor, not a reversed multiplication. -/
theorem dmul_inr_eq_of_inr {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) {a b : Fin n}
    (hya : y (Sum.inr a) = Sum.inr b) :
    Challenge.dmul x y (Sum.inr a) = Sum.inr b := by
  by_cases hba : b = a
  · subst b
    apply DiagramProduct.dmul_eq_self_of_no_partner x y (Sum.inr a)
    intro q hq hreach
    rw [StackGeometry.stackGraph_eq_movingGraph hx hy] at hreach
    have hupper : StackGeometry.upperPerm hx (Challenge.outer (Sum.inr a)) =
        Challenge.outer (Sum.inr a) := rfl
    have hlower : StackGeometry.lowerPerm hy (Challenge.outer (Sum.inr a)) =
        Challenge.outer (Sum.inr a) := by
      change StackGeometry.lowerMap y (Challenge.lower (Sum.inr a)) =
        Challenge.lower (Sum.inr a)
      rw [StackGeometry.lowerMap_lower, hya]
    have heq := reachable_eq_of_common_fixed (StackGeometry.upperPerm hx)
      (StackGeometry.lowerPerm hy) (StackGeometry.upperMap_involutive hx)
      (StackGeometry.lowerMap_involutive hy) hupper hlower hreach
    exact hq (StackGeometry.outer_injective heq)
  · have hne : (Sum.inr b : Challenge.Pt n) ≠ Sum.inr a :=
      fun h => hba (Sum.inr.inj h)
    have hreach : (Challenge.stackGraph x y).Reachable
        (Challenge.outer (Sum.inr a)) (Challenge.outer (Sum.inr b)) := by
      apply DiagramUnits.reachable_of_stackEdge x y
      exact Or.inr ⟨Sum.inr a, rfl, by simp only [hya, Challenge.lower, Challenge.outer]⟩
    apply DiagramProduct.dmul_eq_of_partner x y (Sum.inr a) (Sum.inr b) hne hreach
    intro q hq hpath
    exact StackGeometry.outer_partner_unique hx hy hq hne hpath hreach

/-- A through block in the product can only start at a genuine through endpoint of x. -/
theorem topFree_dmul_subset {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) :
    (Challenge.topHalf (Challenge.dmul x y)).1 ⊆ (Challenge.topHalf x).1 := by
  intro a ha
  have hthrough := (DiagramExtraction.mem_topFree_iff (Challenge.dmul x y) a).mp ha
  apply (DiagramExtraction.mem_topFree_iff x a).mpr
  cases hxa : x (Sum.inl a) with
  | inl b =>
    have heq := dmul_inl_eq_of_inl hx hy hxa
    simp only [heq, Sum.isRight_inl, Bool.false_eq_true] at hthrough
  | inr b => rfl

/-- A through block in the product can only end at a genuine through endpoint of y. -/
theorem botFree_dmul_subset {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) :
    (Challenge.botHalf (Challenge.dmul x y)).1 ⊆ (Challenge.botHalf y).1 := by
  intro a ha
  have hthrough := (DiagramExtraction.mem_botFree_iff (Challenge.dmul x y) a).mp ha
  apply (DiagramExtraction.mem_botFree_iff y a).mpr
  cases hya : y (Sum.inr a) with
  | inl b => rfl
  | inr b =>
    have heq := dmul_inr_eq_of_inr hx hy hya
    simp only [heq, Sum.isLeft_inr, Bool.false_eq_true] at hthrough

theorem rank_dmul_le_left {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) :
    Challenge.rank (Challenge.dmul x y) ≤ Challenge.rank x := by
  change (Challenge.topHalf (Challenge.dmul x y)).1.card ≤ (Challenge.topHalf x).1.card
  exact Finset.card_le_card (topFree_dmul_subset hx hy)

/-- The right bound uses the real top/bottom through-block equivalence for both involutions. -/
theorem rank_dmul_le_right {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y) :
    Challenge.rank (Challenge.dmul x y) ≤ Challenge.rank y := by
  calc
    Challenge.rank (Challenge.dmul x y) =
        (Challenge.botHalf (Challenge.dmul x y)).1.card :=
      DiagramExtraction.top_bot_free_card (Challenge.dmul x y) (DiagramProduct.dmul_isPB hx hy)
    _ ≤ (Challenge.botHalf y).1.card := Finset.card_le_card (botFree_dmul_subset hx hy)
    _ = Challenge.rank y := (DiagramExtraction.top_bot_free_card y hy).symm

/-- Exactly the frozen RankMul statement, for every n and every pair of PB diagrams. -/
theorem check_RankMul : Challenge.RankMul := by
  intro n x hx y hy
  exact le_min (rank_dmul_le_left hx hy) (rank_dmul_le_right hx hy)

#print axioms CodexPaper5.DiagramRank.reachable_eq_of_common_fixed
#print axioms CodexPaper5.DiagramRank.dmul_inl_eq_of_inl
#print axioms CodexPaper5.DiagramRank.dmul_inr_eq_of_inr
#print axioms CodexPaper5.DiagramRank.topFree_dmul_subset
#print axioms CodexPaper5.DiagramRank.botFree_dmul_subset
#print axioms CodexPaper5.DiagramRank.rank_dmul_le_left
#print axioms CodexPaper5.DiagramRank.rank_dmul_le_right
#print axioms CodexPaper5.DiagramRank.check_RankMul

end CodexPaper5.DiagramRank
