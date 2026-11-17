import Research.TaskH.Seven.SevenTwoColorOwnHubs

/-! The actual four-pool residual set. Cardinal upper bounds are owned by
the independent source branch; none is built into this definition. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def DegreeTwelveFrame.residualPool {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Finset V :=
  rootOutside G v \ (F.centerPool 0 ∪ F.centerPool 1 ∪ F.splitPoolA ∪ F.splitPoolB)

theorem DegreeTwelveFrame.mem_residualPool_iff {v z : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : z ∈ F.residualPool ↔
      z ∈ rootOutside G v ∧ z ∉ F.centerPool 0 ∧ z ∉ F.centerPool 1 ∧
      z ∉ F.splitPoolA ∧ z ∉ F.splitPoolB := by
  simp only [DegreeTwelveFrame.residualPool, Finset.mem_sdiff, Finset.mem_union,
    not_or, and_assoc]

theorem DegreeTwelveFrame.residualPool_no_root_neighbor {v z : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hz : z ∈ F.residualPool)
    (w : G.neighborSet v) : ¬ G.Adj z w.val := by
  intro hzw
  obtain ⟨hzO, hzA, hzB, hzX, hzY⟩ := F.mem_residualPool_iff.mp hz
  let wd := twoColorNeighborDeleted v w
  rcases F.neighbor_cases w with ⟨j, hj⟩ | ⟨i, e, hie⟩
  · have hadj : G.Adj (F.center j).val z := by rw [hj]; exact hzw.symm
    have hm : z ∈ F.centerPool j := Finset.mem_filter.mpr ⟨hzO, hadj⟩
    fin_cases j
    · exact hzA hm
    · exact hzB hm
  · have hcolor : c wd = (F.pairIndex i).val := by
      change neighborColor v c w = (F.pairIndex i).val
      rw [← hie]
      exact F.leaf_color i e
    rcases (F.pair_fiber_as_deleted i wd w.property).mp hcolor with he | he
    · exact hzX (Finset.mem_filter.mpr ⟨hzO, i, by
        have hv := congrArg Subtype.val he
        change w.val = (F.splitA i).val at hv
        rw [← hv]; exact hzw⟩)
    · exact hzY (Finset.mem_filter.mpr ⟨hzO, i, by
        have hv := congrArg Subtype.val he
        change w.val = (F.splitB i).val at hv
        rw [← hv]; exact hzw⟩)

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.residualPool
#print axioms TaskH.Seven.DegreeTwelveFrame.mem_residualPool_iff
#print axioms TaskH.Seven.DegreeTwelveFrame.residualPool_no_root_neighbor
