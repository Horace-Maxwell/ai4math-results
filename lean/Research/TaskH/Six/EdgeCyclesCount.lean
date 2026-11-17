import Research.TaskH.Six.EdgeCyclesDistinct
import Research.TaskH.FiniteBudget

/-!
E for k=6 is a double count on the graph's actual unoriented cycle edge
sets. Each of 720 orders has a genuine witness; a fixed edge set admits
at most twelve orders, so at least sixty different edge sets occur.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} {G : SimpleGraph V}

/-- The coloring is kept explicit so singleton constructions use the same
actual deleted-edge coloring, rather than an unrelated existential one. -/
theorem critical_coloring_sixty_modCyclesThroughAvoid [Fintype V]
    (h : IsCriticalPlus 6 G) (hs : ShortSixCycles G) {x y : V} (hxy : G.Adj x y)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 6)) :
    60 ≤ (TaskH.modCyclesThroughAvoid 6 G x y).ncard := by
  classical
  let A : Finset (Equiv.Perm (Fin 6)) := Finset.univ
  let C := (Set.toFinite (TaskH.modCyclesThroughAvoid 6 G x y)).toFinset
  let R : Equiv.Perm (Fin 6) → Finset (Sym2 V) → Prop :=
    fun π s => π ∈ basedCycleOrders (G := G) c x s
  have hA : A.card = 720 := by norm_num [A, Fintype.card_perm]
  have hrow : ∀ π ∈ A, 1 ≤ (C.filter (R π)).card := by
    intro π _hπ
    obtain ⟨p, hp, hlen, hf, hy⟩ := critical_edge_ordered_six_cycle h hs hxy c π
    have hm : p.edges.toFinset ∈ C.filter (R π) := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact (Set.toFinite _).mem_toFinset.mpr
          (mem_modCyclesThroughAvoid_of_cycle hp hlen hy)
      · apply (mem_basedCycleOrders c x p.edges.toFinset π).mpr
        exact ⟨p, hp, hlen, p.coe_edges_toFinset.symm, hf⟩
    have hpos := Finset.card_pos.mpr ⟨p.edges.toFinset, hm⟩
    omega
  have hcol : ∀ s ∈ C, (A.filter (fun π => R π s)).card ≤ 12 := by
    intro s _hs
    have he : A.filter (fun π => R π s) = basedCycleOrders (G := G) c x s := by
      ext π
      simp only [A, R, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he]
    exact basedCycleOrders_card_le_twelve c x s
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
  have hhigh : (∑ s ∈ C, (A.filter (fun π => R π s)).card) ≤ C.card * 12 := by
    calc
      _ ≤ ∑ _s ∈ C, 12 := Finset.sum_le_sum hcol
      _ = C.card * 12 := by simp
  have hmid : (∑ π ∈ A, (C.filter (R π)).card) ≤
      ∑ s ∈ C, (A.filter (fun π => R π s)).card := le_of_eq hdouble
  have htotal : (∑ π ∈ A, (C.filter (R π)).card) ≤ C.card * 12 :=
    Nat.le_trans hmid hhigh
  have hn : 720 ≤ C.card * 12 := by
    rw [hA] at hlow
    exact Nat.le_trans hlow htotal
  have hC : C.card = (TaskH.modCyclesThroughAvoid 6 G x y).ncard :=
    (Set.ncard_eq_toFinset_card (TaskH.modCyclesThroughAvoid 6 G x y)
      (Set.toFinite (TaskH.modCyclesThroughAvoid 6 G x y))).symm
  rw [hC] at hn
  omega

theorem critical_edge_sixty_modCyclesThroughAvoid [Fintype V]
    (h : IsCriticalPlus 6 G) (hs : ShortSixCycles G) {x y : V} (hxy : G.Adj x y) :
    60 ≤ (TaskH.modCyclesThroughAvoid 6 G x y).ncard := by
  obtain ⟨c⟩ := critical_colorable_deletedEdge h hxy
  exact critical_coloring_sixty_modCyclesThroughAvoid h hs hxy c

end TaskH.Six

#print axioms TaskH.Six.critical_coloring_sixty_modCyclesThroughAvoid
#print axioms TaskH.Six.critical_edge_sixty_modCyclesThroughAvoid
