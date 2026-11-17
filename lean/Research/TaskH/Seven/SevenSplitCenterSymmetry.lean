import Research.TaskH.Seven.SevenSplitCenterPools

/-! Center interchange is an actual coordinate operation on the same graph,
root and deleted coloring. It transports the asymmetric path statements. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.swapCenters_pureSplit {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) : F.swapCenters.IsPureSplit := by
  intro i
  rcases hF i with h | h
  · right
    simpa only [F.swapCenters_center_zero, F.swapCenters_center_one,
      F.swapCenters_leaf] using And.intro h.2.2.1 (And.intro h.2.2.2 (And.intro h.1 h.2.1))
  · left
    simpa only [F.swapCenters_center_zero, F.swapCenters_center_one,
      F.swapCenters_leaf] using And.intro h.2.2.1 (And.intro h.2.2.2 (And.intro h.1 h.2.1))

theorem DegreeTwelveFrame.swapCenters_splitA {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5) :
    F.swapCenters.splitA i = F.splitB i := by
  rcases hF i with h | h <;>
    simp [DegreeTwelveFrame.splitA, DegreeTwelveFrame.splitB,
      F.swapCenters_center_zero, F.swapCenters_leaf, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem DegreeTwelveFrame.swapCenters_splitB {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5) :
    F.swapCenters.splitB i = F.splitA i := by
  rcases hF i with h | h <;>
    simp [DegreeTwelveFrame.splitA, DegreeTwelveFrame.splitB,
      F.swapCenters_center_zero, F.swapCenters_leaf, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem DegreeTwelveFrame.swapCenters_centerPool_zero {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : F.swapCenters.centerPool 0 = F.centerPool 1 := by
  simp only [DegreeTwelveFrame.centerPool, F.swapCenters_center_zero]

theorem DegreeTwelveFrame.swapCenters_centerPool_one {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : F.swapCenters.centerPool 1 = F.centerPool 0 := by
  simp only [DegreeTwelveFrame.centerPool, F.swapCenters_center_one]

theorem DegreeTwelveFrame.swapCenters_splitPoolA {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    F.swapCenters.splitPoolA = F.splitPoolB := by
  simp only [DegreeTwelveFrame.splitPoolA, DegreeTwelveFrame.splitPoolB,
    F.swapCenters_splitA hF]

theorem DegreeTwelveFrame.swapCenters_splitPoolB {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    F.swapCenters.splitPoolB = F.splitPoolA := by
  simp only [DegreeTwelveFrame.splitPoolA, DegreeTwelveFrame.splitPoolB,
    F.swapCenters_splitB hF]

theorem DegreeTwelveFrame.pureSplit_centerPool_one_disjoint_A
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    Disjoint (F.centerPool 1) F.splitPoolA := by
  have h := F.swapCenters.pureSplit_centerPool_zero_disjoint_B hr
    (F.swapCenters_pureSplit hF)
  simpa only [F.swapCenters_centerPool_zero, F.swapCenters_splitPoolB hF] using h

theorem DegreeTwelveFrame.pureSplit_centerPool_one_no_A_pool_edge
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (z w : V) (hz : z ∈ F.centerPool 1) (hw : w ∈ F.splitPoolA) :
    ¬ G.Adj z w := by
  have hz' : z ∈ F.swapCenters.centerPool 0 := by
    simpa only [F.swapCenters_centerPool_zero] using hz
  have hw' : w ∈ F.swapCenters.splitPoolB := by
    simpa only [F.swapCenters_splitPoolB hF] using hw
  exact F.swapCenters.pureSplit_centerPool_zero_no_B_pool_edge hr
    (F.swapCenters_pureSplit hF) z w hz' hw'

end TaskH.Seven

#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_pureSplit
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_splitA
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_splitB
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_centerPool_zero
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_centerPool_one
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_splitPoolA
#print axioms TaskH.Seven.DegreeTwelveFrame.swapCenters_splitPoolB
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_centerPool_one_disjoint_A
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_centerPool_one_no_A_pool_edge
