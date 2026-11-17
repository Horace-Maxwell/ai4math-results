import Research.TaskH.Seven.SevenSplitResidualBudget
import Research.TaskH.Seven.SevenTwoColorResidualLowerBound

/-! The degree-twelve contradiction on the original graph. The actual
deleted coloring, frame, pure split and residual upper bound are all
derived internally, on the same witnesses used by the residual lower bound. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem equality_degree_twelve_false
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V) (hv : G.degree v = 12) : False := by
  classical
  obtain ⟨c⟩ := TaskH.critical_colorable_deletedVertex hcrit v
  obtain ⟨F⟩ := equality_degreeTwelveFrame hcrit hc hnot v c hv
  have hF : F.IsPureSplit := equality_degreeTwelve_pureSplit hcrit hc hnot v c hv F
  have hsmall : F.residualPool.card ≤ 7 :=
    equality_degreeTwelve_residualPool_card_le_seven hcrit hc hnot v c hv F
  exact equality_fixed_pureSplit_false_of_residual_card hcrit hc hnot hv F hF hsmall

theorem equality_noncomplete_degree_ge_thirteen
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V) : 13 ≤ G.degree v := by
  have h12 := equality_noncomplete_degree_ge_twelve hcrit hc hnot v
  by_contra hlt
  have hv : G.degree v = 12 := by omega
  exact equality_degree_twelve_false hcrit hc hnot v hv

end TaskH.Seven

#print axioms TaskH.Seven.equality_degree_twelve_false
#print axioms TaskH.Seven.equality_noncomplete_degree_ge_thirteen
