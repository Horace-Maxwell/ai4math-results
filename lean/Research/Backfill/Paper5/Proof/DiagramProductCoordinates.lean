import Research.Backfill.Paper5.Proof.DiagramMultiplication
import Research.Backfill.Paper5.Proof.GammaCompatibility

set_option autoImplicit false

namespace CodexPaper5.DiagramProductCoordinates

open BackfillPaper5

/-- Following actual through blocks and the actual middle path represents the product
permutation in the frozen right-action convention. -/
theorem repG_dmul_product {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r)
    (hc : Challenge.Compat (Challenge.botHalf x) (Challenge.topHalf y)) :
    Challenge.RepG r (Challenge.dmul x y)
      (Challenge.gCoord r x * Challenge.pSand r (Challenge.botHalf x) (Challenge.topHalf y) *
        Challenge.gCoord r y) := by
  have hxPB := DiagramExtraction.isPB_of_mem_Jr hx
  have hyPB := DiagramExtraction.isPB_of_mem_Jr hy
  have hpPB := DiagramProduct.dmul_isPB hxPB hyPB
  have ht := DiagramMultiplication.topHalf_dmul_of_compat hx hy hc
  have hb := DiagramMultiplication.botHalf_dmul_of_compat hx hy hc
  have hgx := DiagramExtraction.repG_gCoord_of_mem_Jr hx
  have hgy := DiagramExtraction.repG_gCoord_of_mem_Jr hy
  have hgp := GammaCompatibility.repP_pSand
    (DiagramExtraction.botHalf_mem_hr hx) (DiagramExtraction.topHalf_mem_hr hy) hc
  intro k a b hab hk
  have hback : Challenge.dmul x y (Sum.inr b) = Sum.inl a := by
    have h := hpPB (Sum.inl a)
    rwa [hab] at h
  have haProd : a ∈ (Challenge.topHalf (Challenge.dmul x y)).1 :=
    (DiagramExtraction.mem_topFree_iff (Challenge.dmul x y) a).mpr (by simp [hab])
  have hbProd : b ∈ (Challenge.botHalf (Challenge.dmul x y)).1 :=
    (DiagramExtraction.mem_botFree_iff (Challenge.dmul x y) b).mpr (by simp [hback])
  have haThrough := (DiagramExtraction.mem_topFree_iff x a).mp
    (DiagramRank.topFree_dmul_subset hxPB hyPB haProd)
  have hbThrough := (DiagramExtraction.mem_botFree_iff y b).mp
    (DiagramRank.botFree_dmul_subset hxPB hyPB hbProd)
  cases hxa : x (Sum.inl a) with
  | inl u => simp [hxa] at haThrough
  | inr u =>
    have hxu : x (Sum.inr u) = Sum.inl a := by
      have h := hxPB (Sum.inl a)
      rwa [hxa] at h
    have hu : u ∈ (Challenge.botHalf x).1 :=
      (DiagramExtraction.mem_botFree_iff x u).mpr (by simp [hxu])
    cases hyb : y (Sum.inr b) with
    | inr e => simp [hyb] at hbThrough
    | inl e =>
      have hye : y (Sum.inl e) = Sum.inr b := by
        have h := hyPB (Sum.inr b)
        rwa [hyb] at h
      have he : e ∈ (Challenge.topHalf y).1 :=
        (DiagramExtraction.mem_topFree_iff y e).mpr (by simp [hye])
      have hpath := (StackGammaProjection.dmul_through_iff hxPB hyPB hxa hye).mp hab
      have hkx : Challenge.pos (Challenge.topHalf x).1 a = k := by
        simpa only [ht] using hk
      let j : Fin r := (MulOpposite.unop (Challenge.gCoord r x)) k
      have hj : (j : ℕ) = Challenge.pos (Challenge.botHalf x).1 u := hgx k a u hxa hkx
      let l : Fin r :=
        (MulOpposite.unop (Challenge.pSand r (Challenge.botHalf x) (Challenge.topHalf y))) j
      have hl : (l : ℕ) = Challenge.pos (Challenge.topHalf y).1 e :=
        hgp j u e hu he hj.symm hpath
      have hlast := hgy l e b hye hl.symm
      dsimp only [l, j] at hlast
      simpa only [MulOpposite.unop_mul, Equiv.Perm.mul_apply, hb] using hlast

/-- Recover the frozen choice-defined coordinate from its actual RepG specification. -/
theorem gCoord_dmul_of_compat {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r)
    (hc : Challenge.Compat (Challenge.botHalf x) (Challenge.topHalf y)) :
    Challenge.gCoord r (Challenge.dmul x y) =
      Challenge.gCoord r x * Challenge.pSand r (Challenge.botHalf x) (Challenge.topHalf y) *
        Challenge.gCoord r y :=
  DiagramExtraction.gCoord_eq_of_repG (DiagramMultiplication.dmul_mem_Jr_of_compat hx hy hc) _
    (repG_dmul_product hx hy hc)

theorem check_Prop31b : Challenge.Prop31b := by
  intro D n r x hx y hy
  refine ⟨DiagramMultiplication.rank_dmul_eq_iff_compat hx hy, ?_⟩
  intro hc
  exact ⟨DiagramMultiplication.topHalf_dmul_of_compat hx hy hc,
    DiagramMultiplication.botHalf_dmul_of_compat hx hy hc, gCoord_dmul_of_compat hx hy hc⟩

#print axioms CodexPaper5.DiagramProductCoordinates.repG_dmul_product
#print axioms CodexPaper5.DiagramProductCoordinates.gCoord_dmul_of_compat
#print axioms CodexPaper5.DiagramProductCoordinates.check_Prop31b

end CodexPaper5.DiagramProductCoordinates
