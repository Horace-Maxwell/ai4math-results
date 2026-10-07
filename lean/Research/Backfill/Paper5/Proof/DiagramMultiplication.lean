import Research.Backfill.Paper5.Proof.StackGammaProjection
import Research.Backfill.Paper5.Proof.DiagramRank

set_option autoImplicit false

namespace CodexPaper5.DiagramMultiplication

open BackfillPaper5 Function

theorem reverse_edge {n : ℕ} {x : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) {p q : Challenge.Pt n} (h : x p = q) : x q = p :=
  (congrArg x h).symm.trans (hx p)

/-- Compatibility preserves every actual top through endpoint of the left factor.
The reverse inclusion is the already proved real-product rank argument. -/
theorem topFree_dmul_eq_of_compat {n : ℕ} {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : Challenge.IsPB x) (hy : Challenge.IsPB y)
    (hc : Challenge.Compat (Challenge.botHalf x) (Challenge.topHalf y)) :
    (Challenge.topHalf (Challenge.dmul x y)).1 = (Challenge.topHalf x).1 := by
  apply Finset.Subset.antisymm (DiagramRank.topFree_dmul_subset hx hy)
  intro a ha
  let aa : DiagramExtraction.TopFree x := ⟨a, ha⟩
  let uu := DiagramExtraction.throughToBot x hx aa
  have hxa : x (Sum.inl a) = Sum.inr uu.val :=
    DiagramExtraction.throughToBot_apply x hx aa
  obtain ⟨e, he, hue⟩ := hc uu.val uu.property
  let ee : DiagramExtraction.TopFree y := ⟨e, he⟩
  let bb := DiagramExtraction.throughToBot y hy ee
  have hye : y (Sum.inl e) = Sum.inr bb.val :=
    DiagramExtraction.throughToBot_apply y hy ee
  have hproduct : Challenge.dmul x y (Sum.inl a) = Sum.inr bb.val :=
    (StackGammaProjection.dmul_through_iff hx hy hxa hye).mpr hue
  apply (DiagramExtraction.mem_topFree_iff (Challenge.dmul x y) a).mpr
  simp [hproduct]

theorem rank_dmul_eq_of_compat {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r)
    (hc : Challenge.Compat (Challenge.botHalf x) (Challenge.topHalf y)) :
    Challenge.rank (Challenge.dmul x y) = r := by
  change (Challenge.topHalf (Challenge.dmul x y)).1.card = r
  rw [topFree_dmul_eq_of_compat
    (DiagramExtraction.isPB_of_mem_Jr hx) (DiagramExtraction.isPB_of_mem_Jr hy) hc]
  exact hx.2

/-- The converse reconstructs actual x-through, product-through, and y-through edges.
Product involutivity is used before the bottom-free subset argument. -/
theorem rank_dmul_eq_iff_compat {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r) :
    Challenge.rank (Challenge.dmul x y) = r ↔
      Challenge.Compat (Challenge.botHalf x) (Challenge.topHalf y) := by
  constructor
  · intro hr
    have hxpb := DiagramExtraction.isPB_of_mem_Jr hx
    have hypb := DiagramExtraction.isPB_of_mem_Jr hy
    have hproductpb := DiagramProduct.dmul_isPB hxpb hypb
    have hfree : (Challenge.topHalf (Challenge.dmul x y)).1 =
        (Challenge.topHalf x).1 := by
      apply Finset.eq_of_subset_of_card_le (DiagramRank.topFree_dmul_subset hxpb hypb)
      change Challenge.rank x ≤ Challenge.rank (Challenge.dmul x y)
      rw [hx.2, hr]
    intro u hu
    let uu : DiagramExtraction.BotFree x := ⟨u, hu⟩
    let aa := DiagramExtraction.throughToTop x hxpb uu
    have hxreverse : x (Sum.inr u) = Sum.inl aa.val :=
      DiagramExtraction.throughToTop_apply x hxpb uu
    have hxa : x (Sum.inl aa.val) = Sum.inr u := reverse_edge hxpb hxreverse
    have haproduct : aa.val ∈ (Challenge.topHalf (Challenge.dmul x y)).1 := by
      rw [hfree]
      exact aa.property
    let ap : DiagramExtraction.TopFree (Challenge.dmul x y) := ⟨aa.val, haproduct⟩
    let bb := DiagramExtraction.throughToBot (Challenge.dmul x y) hproductpb ap
    have hpab : Challenge.dmul x y (Sum.inl aa.val) = Sum.inr bb.val :=
      DiagramExtraction.throughToBot_apply (Challenge.dmul x y) hproductpb ap
    have hby : bb.val ∈ (Challenge.botHalf y).1 :=
      DiagramRank.botFree_dmul_subset hxpb hypb bb.property
    let byy : DiagramExtraction.BotFree y := ⟨bb.val, hby⟩
    let ee := DiagramExtraction.throughToTop y hypb byy
    have hyreverse : y (Sum.inr bb.val) = Sum.inl ee.val :=
      DiagramExtraction.throughToTop_apply y hypb byy
    have hye : y (Sum.inl ee.val) = Sum.inr bb.val := reverse_edge hypb hyreverse
    exact ⟨ee.val, ee.property,
      (StackGammaProjection.dmul_through_iff hxpb hypb hxa hye).mp hpab⟩
  · exact rank_dmul_eq_of_compat hx hy

/-- Equality of the bottom free sets uses the true top/bottom equivalence and equal ranks. -/
theorem botFree_dmul_eq_of_compat {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r)
    (hc : Challenge.Compat (Challenge.botHalf x) (Challenge.topHalf y)) :
    (Challenge.botHalf (Challenge.dmul x y)).1 = (Challenge.botHalf y).1 := by
  have hxpb := DiagramExtraction.isPB_of_mem_Jr hx
  have hypb := DiagramExtraction.isPB_of_mem_Jr hy
  apply Finset.eq_of_subset_of_card_le (DiagramRank.botFree_dmul_subset hxpb hypb)
  have hpcard : (Challenge.botHalf (Challenge.dmul x y)).1.card = r :=
    (DiagramExtraction.top_bot_free_card (Challenge.dmul x y)
      (DiagramProduct.dmul_isPB hxpb hypb)).symm.trans (rank_dmul_eq_of_compat hx hy hc)
  have hycard : (Challenge.botHalf y).1.card = r := (DiagramExtraction.botHalf_mem_hr hy).1
  exact le_of_eq (hycard.trans hpcard.symm)

/-- Full top half equality, including its involution map rather than just its free set. -/
theorem topHalf_dmul_of_compat {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r)
    (hc : Challenge.Compat (Challenge.botHalf x) (Challenge.topHalf y)) :
    Challenge.topHalf (Challenge.dmul x y) = Challenge.topHalf x := by
  have hxpb := DiagramExtraction.isPB_of_mem_Jr hx
  have hypb := DiagramExtraction.isPB_of_mem_Jr hy
  have hfree := topFree_dmul_eq_of_compat hxpb hypb hc
  apply Prod.ext hfree
  funext a
  cases hxa : x (Sum.inl a) with
  | inl b =>
    have hp := DiagramRank.dmul_inl_eq_of_inl hxpb hypb hxa
    simp only [Challenge.topHalf, hp, hxa]
  | inr u =>
    have ha : a ∈ (Challenge.topHalf x).1 :=
      (DiagramExtraction.mem_topFree_iff x a).mpr (by simp [hxa])
    have hap : a ∈ (Challenge.topHalf (Challenge.dmul x y)).1 := by rw [hfree]; exact ha
    have hright := (DiagramExtraction.mem_topFree_iff (Challenge.dmul x y) a).mp hap
    cases hp : Challenge.dmul x y (Sum.inl a) with
    | inl b => simp only [hp, Sum.isRight_inl, Bool.false_eq_true] at hright
    | inr b => simp only [Challenge.topHalf, hp, hxa]

/-- Full bottom half equality, in the original multiplication order x above y. -/
theorem botHalf_dmul_of_compat {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r)
    (hc : Challenge.Compat (Challenge.botHalf x) (Challenge.topHalf y)) :
    Challenge.botHalf (Challenge.dmul x y) = Challenge.botHalf y := by
  have hxpb := DiagramExtraction.isPB_of_mem_Jr hx
  have hypb := DiagramExtraction.isPB_of_mem_Jr hy
  have hfree := botFree_dmul_eq_of_compat hx hy hc
  apply Prod.ext hfree
  funext a
  cases hya : y (Sum.inr a) with
  | inl e =>
    have ha : a ∈ (Challenge.botHalf y).1 :=
      (DiagramExtraction.mem_botFree_iff y a).mpr (by simp [hya])
    have hap : a ∈ (Challenge.botHalf (Challenge.dmul x y)).1 := by rw [hfree]; exact ha
    have hleft := (DiagramExtraction.mem_botFree_iff (Challenge.dmul x y) a).mp hap
    cases hp : Challenge.dmul x y (Sum.inr a) with
    | inl b => simp only [Challenge.botHalf, hp, hya]
    | inr b => simp only [hp, Sum.isLeft_inr, Bool.false_eq_true] at hleft
  | inr b =>
    have hp := DiagramRank.dmul_inr_eq_of_inr hxpb hypb hya
    simp only [Challenge.botHalf, hp, hya]

/-- Actual PB/B closure and the established rank equality give membership in the frozen Jr. -/
theorem dmul_mem_Jr_of_compat {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r)
    (hc : Challenge.Compat (Challenge.botHalf x) (Challenge.topHalf y)) :
    Challenge.dmul x y ∈ Challenge.Jr D n r := by
  refine ⟨?_, rank_dmul_eq_of_compat hx hy hc⟩
  cases D with
  | B => exact DiagramProduct.dmul_mem_B hx.1 hy.1
  | PB => exact DiagramProduct.dmul_isPB hx.1 hy.1

#print axioms CodexPaper5.DiagramMultiplication.reverse_edge
#print axioms CodexPaper5.DiagramMultiplication.topFree_dmul_eq_of_compat
#print axioms CodexPaper5.DiagramMultiplication.rank_dmul_eq_of_compat
#print axioms CodexPaper5.DiagramMultiplication.rank_dmul_eq_iff_compat
#print axioms CodexPaper5.DiagramMultiplication.botFree_dmul_eq_of_compat
#print axioms CodexPaper5.DiagramMultiplication.topHalf_dmul_of_compat
#print axioms CodexPaper5.DiagramMultiplication.botHalf_dmul_of_compat
#print axioms CodexPaper5.DiagramMultiplication.dmul_mem_Jr_of_compat

end CodexPaper5.DiagramMultiplication
