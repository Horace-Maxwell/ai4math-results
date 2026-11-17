import Research.TaskH.Seven.EdgeCyclesDistinct
import Research.TaskH.FiniteBudget

/-!
E for k=7 is a double count on the graph's actual unoriented cycle edge
sets. Each of 5040 orders has a genuine witness; a fixed edge set admits
at most fourteen orders, so at least 360 different edge sets occur.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} {G : SimpleGraph V}

/-- The coloring is kept explicit so singleton constructions use the same
actual deleted-edge coloring, rather than an unrelated existential one. -/
theorem critical_coloring_three_hundred_sixty_modCyclesThroughAvoid [Fintype V]
    (h : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) {x y : V} (hxy : G.Adj x y)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) :
    360 ≤ (TaskH.modCyclesThroughAvoid 7 G x y).ncard := by
  classical
  let A : Finset (Equiv.Perm (Fin 7)) := Finset.univ
  let C := (Set.toFinite (TaskH.modCyclesThroughAvoid 7 G x y)).toFinset
  let R : Equiv.Perm (Fin 7) → Finset (Sym2 V) → Prop :=
    fun π s => π ∈ basedCycleOrders (G := G) c x s
  have hA : A.card = 5040 := by norm_num [A, Fintype.card_perm]
  have hrow : ∀ π ∈ A, 1 ≤ (C.filter (R π)).card := by
    intro π _hπ
    obtain ⟨p, hp, hlen, hf, hy⟩ := critical_edge_ordered_seven_cycle h hs hxy c π
    have hm : p.edges.toFinset ∈ C.filter (R π) := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact (Set.toFinite _).mem_toFinset.mpr
          (mem_modCyclesThroughAvoid_of_cycle hp hlen hy)
      · apply (mem_basedCycleOrders c x p.edges.toFinset π).mpr
        exact ⟨p, hp, hlen, p.coe_edges_toFinset.symm, hf⟩
    have hpos := Finset.card_pos.mpr ⟨p.edges.toFinset, hm⟩
    omega
  have hcol : ∀ s ∈ C, (A.filter (fun π => R π s)).card ≤ 14 := by
    intro s _hs
    have he : A.filter (fun π => R π s) = basedCycleOrders (G := G) c x s := by
      ext π
      simp only [A, R, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he]
    exact basedCycleOrders_card_le_fourteen c x s
  have hdouble : (∑ π ∈ A, (C.filter (R π)).card) =
      ∑ s ∈ C, (A.filter (fun π => R π s)).card := by
    convert FiniteBudget.relation_double_count A C R using 1 <;>
      apply Finset.sum_congr rfl
    all_goals
      intro z _
      congr 1
      ext w
      simp only [Finset.mem_filter]
  have hlow : A.card ≤ ∑ π ∈ A, (C.filter (R π)).card := by
    calc
      A.card = ∑ _π ∈ A, 1 := by simp
      _ ≤ ∑ π ∈ A, (C.filter (R π)).card := Finset.sum_le_sum hrow
  have hhigh : (∑ s ∈ C, (A.filter (fun π => R π s)).card) ≤ C.card * 14 := by
    calc
      _ ≤ ∑ _s ∈ C, 14 := Finset.sum_le_sum hcol
      _ = C.card * 14 := by simp
  have hmid : (∑ π ∈ A, (C.filter (R π)).card) ≤
      ∑ s ∈ C, (A.filter (fun π => R π s)).card := le_of_eq hdouble
  have htotal : (∑ π ∈ A, (C.filter (R π)).card) ≤ C.card * 14 :=
    Nat.le_trans hmid hhigh
  have hn : 5040 ≤ C.card * 14 := by
    rw [hA] at hlow
    exact Nat.le_trans hlow htotal
  have hC : C.card = (TaskH.modCyclesThroughAvoid 7 G x y).ncard :=
    (Set.ncard_eq_toFinset_card (TaskH.modCyclesThroughAvoid 7 G x y)
      (Set.toFinite (TaskH.modCyclesThroughAvoid 7 G x y))).symm
  rw [hC] at hn
  omega

theorem critical_edge_three_hundred_sixty_modCyclesThroughAvoid [Fintype V]
    (h : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) {x y : V} (hxy : G.Adj x y) :
    360 ≤ (TaskH.modCyclesThroughAvoid 7 G x y).ncard := by
  obtain ⟨c⟩ := critical_colorable_deletedEdge h hxy
  exact critical_coloring_three_hundred_sixty_modCyclesThroughAvoid h hs hxy c

end TaskH.Seven

#print axioms TaskH.Seven.critical_coloring_three_hundred_sixty_modCyclesThroughAvoid
#print axioms TaskH.Seven.critical_edge_three_hundred_sixty_modCyclesThroughAvoid
