import Research.TaskH.Seven.SevenCommonPartners

/-! Local three-representative P7 transport. Only actual common-color
subtype members are used: no nonexistent fifth common representative. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem three_common_representatives_outside_color_constraints
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i j k : ↥F.commonColors)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v))
    (hzi : G.Adj z.val (F.commonRep i).val)
    (hzj : G.Adj z.val (F.commonRep j).val) :
    c z ≠ neighborColor v c (F.center 0) ∧
      c z ≠ neighborColor v c (F.center 1) ∧
      c z ≠ (F.pairIndex i.val).val ∧ c z ≠ (F.pairIndex j.val).val ∧
      c z ≠ (F.pairIndex k.val).val := by
  have hvals : i.val ≠ j.val := fun he => hij (Subtype.ext he)
  have hikvals : i.val ≠ k.val := fun he => hik (Subtype.ext he)
  have hjkvals : j.val ≠ k.val := fun he => hjk (Subtype.ext he)
  have hxy : (F.commonRep i).val ≠ (F.commonRep j).val :=
    F.leaf_leaf_ne hvals (F.commonRepSide i) (F.commonRepSide j)
  have H := split_pool_two_leaf_constraints_at_zero hr F i.val j.val k.val hikvals hjkvals
    (F.commonRepSide i) (F.commonRepSide j) (F.commonRepSide k) hxy
    (F.commonRep_adj_zero j) (F.commonRep_adj_zero k) (F.commonRep_adj_one k) z hz hzi hzj
  have hpi : c z ≠ neighborColor v c (F.commonRep i) := c.valid hzi
  have hpj : c z ≠ neighborColor v c (F.commonRep j) := c.valid hzj
  refine ⟨H.2.1, H.2.2.1, ?_, ?_, H.2.2.2⟩
  · simpa only [F.commonRep_color] using hpi
  · simpa only [F.commonRep_color] using hpj

end TaskH.Seven
#print axioms TaskH.Seven.three_common_representatives_outside_color_constraints
