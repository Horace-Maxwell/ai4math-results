import Research.TaskH.Five.EdgeCyclesDistinct

/-!
The twelve critical-edge cycles are distinct as actual undirected edge sets.
ShortFiveCycles remains an intermediate conclusion to be proved from equality.
No assumption about an abstract cycle count is introduced here.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open _root_.TaskH.Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem critical_edge_twelve_cycle_witnesses [DecidableEq V]
    (h : IsCriticalPlus 5 G) (hs : ShortFiveCycles G) {x y : V} (hxy : G.Adj x y) :
    ∃ P : Fin 12 → G.Walk x x,
      (∀ i, (P i).IsCycle ∧ (P i).length = 5 ∧ y ∉ (P i).support) ∧
        Function.Injective (fun i => (P i).edges.toFinset) := by
  classical
  obtain ⟨c⟩ := critical_colorable_deletedEdge h hxy
  have hex : ∀ i : Fin 12, ∃ q : G.Walk x x, q.IsCycle ∧ q.length = 5 ∧
      Follows q c (fiveColorCycle i) ∧ y ∉ q.support :=
    fun i => critical_edge_five_cycle h hs hxy c i
  choose P hp hl hf hy using hex
  refine ⟨P, (fun i => ⟨hp i, hl i, hy i⟩), ?_⟩
  intro i j he
  exact follows_five_cycles_index_eq (hp i) (hp j) (hl i) c i j (hf i) (hf j) he

/-- E for k=5, in the actual frozen edge-set collection and with genuine
vertex membership on the edges. -/
theorem critical_edge_twelve_modCyclesThroughAvoid [Fintype V]
    (h : IsCriticalPlus 5 G) (hs : ShortFiveCycles G) {x y : V} (hxy : G.Adj x y) :
    12 ≤ (modCyclesThroughAvoid 5 G x y).ncard := by
  classical
  obtain ⟨P, hp, hinj⟩ := critical_edge_twelve_cycle_witnesses h hs hxy
  let E : Fin 12 → Finset (Sym2 V) := fun i => (P i).edges.toFinset
  have hE : ∀ i, E i ∈ modCyclesThroughAvoid 5 G x y := by
    intro i
    exact mem_modCyclesThroughAvoid_of_cycle (hp i).1 (hp i).2.1 (hp i).2.2
  have hcard : (Finset.univ.image E).card = 12 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : (((Finset.univ.image E) : Finset (Finset (Sym2 V))) :
      Set (Finset (Sym2 V))) ⊆ modCyclesThroughAvoid 5 G x y := by
    intro s hs
    obtain ⟨i, _, his⟩ := Finset.mem_image.mp hs
    rw [← his]
    exact hE i
  have hn := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at hn
  exact hn

end TaskH.Five

#print axioms TaskH.Five.critical_edge_twelve_cycle_witnesses
#print axioms TaskH.Five.critical_edge_twelve_modCyclesThroughAvoid
