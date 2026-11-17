import Research.TaskH.EdgeCyclesDistinct

/-!
The three critical-edge cycles are distinct as actual undirected edge sets.
ShortFourCycles remains an intermediate conclusion to be proved from equality.
No assumption about an abstract cycle count is introduced here.
-/

set_option autoImplicit false

universe u

namespace TaskH

open Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem critical_edge_three_cycle_witnesses [DecidableEq V]
    (h : IsCriticalPlus 4 G) (hs : ShortFourCycles G) {x y : V} (hxy : G.Adj x y) :
    ∃ P : Fin 3 → G.Walk x x,
      (∀ i, (P i).IsCycle ∧ (P i).length = 4 ∧ y ∉ (P i).support) ∧
        Function.Injective (fun i => (P i).edges.toFinset) := by
  classical
  obtain ⟨c⟩ := critical_colorable_deletedEdge h hxy
  have hex : ∀ i : Fin 3, ∃ q : G.Walk x x, q.IsCycle ∧ q.length = 4 ∧
      Follows q c (fourColorCycle i) ∧ y ∉ q.support :=
    fun i => critical_edge_four_cycle h hs hxy c i
  choose P hp hl hf hy using hex
  refine ⟨P, (fun i => ⟨hp i, hl i, hy i⟩), ?_⟩
  intro i j he
  exact follows_four_cycles_index_eq (hp i) (hp j) (hl i) c i j (hf i) (hf j) he

/-- E for k=4, in the actual frozen edge-set collection and with genuine
vertex membership on the edges. -/
theorem critical_edge_three_modCyclesThroughAvoid [Fintype V]
    (h : IsCriticalPlus 4 G) (hs : ShortFourCycles G) {x y : V} (hxy : G.Adj x y) :
    3 ≤ (modCyclesThroughAvoid 4 G x y).ncard := by
  classical
  obtain ⟨P, hp, hinj⟩ := critical_edge_three_cycle_witnesses h hs hxy
  let E : Fin 3 → Finset (Sym2 V) := fun i => (P i).edges.toFinset
  have hE : ∀ i, E i ∈ modCyclesThroughAvoid 4 G x y := by
    intro i
    exact mem_modCyclesThroughAvoid_of_cycle (hp i).1 (hp i).2.1 (hp i).2.2
  have hcard : (Finset.univ.image E).card = 3 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : (((Finset.univ.image E) : Finset (Finset (Sym2 V))) :
      Set (Finset (Sym2 V))) ⊆ modCyclesThroughAvoid 4 G x y := by
    intro s hs
    obtain ⟨i, _, his⟩ := Finset.mem_image.mp hs
    rw [← his]
    exact hE i
  have hn := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at hn
  exact hn

end TaskH

#print axioms TaskH.critical_edge_three_cycle_witnesses
#print axioms TaskH.critical_edge_three_modCyclesThroughAvoid
