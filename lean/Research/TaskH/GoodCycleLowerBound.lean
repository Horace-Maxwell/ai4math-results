import Research.TaskH.LayerCycles
import Research.TaskH.LayerFlux
import Research.TaskH.LayerCycleSeparation

/-!
The actual five-good-cycles lower bound for each deleted-vertex coloring
and each color order. All five witnesses are genuine graph cycles; their
unoriented edge sets are injected into the frozen modulo-four cycle set.
-/

universe u

namespace TaskH.GoodCycles

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {v : V}

open scoped Classical in
theorem good_mod_cycles_card_ge_five [Fintype V] (hnot : ¬ G.Colorable 4)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (π : Equiv.Perm (Fin 4)) :
    5 ≤ (((Basics.modCycleEdgeSets_finite 4 G).toFinset).filter
      (GoodCycleOrder c π)).card := by
  classical
  have hex : ∀ j : Fin 5, ∃ t : V,
      t ∈ LayerColoring.Ti c π j.val \ LayerColoring.Ti c π (j.val + 1) ∧
      ∃ p : G.Walk t t, p.IsCycle ∧
        Follows p (LayerColoring.shiftedColor c π (j.val + 1)) (finRotate 4) := by
    intro j
    have hj := j.isLt
    have hrange : 1 ≤ j.val + 1 ∧ j.val + 1 ≤ 5 := by omega
    obtain ⟨t, ht, p, hp, hf⟩ := LayerCycles.exists_layer_cycle c π hnot hrange
    refine ⟨t, ?_, p, hp, hf⟩
    simpa only [Nat.add_sub_cancel] using ht
  choose t ht p hp hf using hex
  have hanti : ∀ {a b : ℕ}, a ≤ b →
      LayerColoring.Ti c π b ⊆ LayerColoring.Ti c π a := by
    intro _a _b hab
    exact LayerSets.T_antitone hab
  have hfbit : ∀ j : Fin 5, Follows (p j)
      (fun z => shiftBit (LayerColoring.baseColor c π z)
        (decide (z ∈ LayerColoring.Ti c π (j.val + 1)))) (finRotate 4) := by
    intro j
    have hfun : LayerColoring.shiftedColor c π (j.val + 1) =
        (fun z => shiftBit (LayerColoring.baseColor c π z)
          (decide (z ∈ LayerColoring.Ti c π (j.val + 1)))) := by
      funext z
      rw [LayerFlux.shiftedColor_eq_shiftBit]
      by_cases hz : z ∈ LayerColoring.Ti c π (j.val + 1) <;>
        simp [LayerFlux.shiftFlag, hz]
    rw [← hfun]
    exact hf j
  have hinj : Function.Injective (fun j : Fin 5 => (p j).edges.toFinset) :=
    layer_cycle_edgeSets_injective (LayerColoring.baseColor c π)
      (LayerColoring.Ti c π) hanti t p hp hfbit ht
  let C : Finset (Finset (Sym2 V)) :=
    ((Basics.modCycleEdgeSets_finite 4 G).toFinset).filter (GoodCycleOrder c π)
  have hmem : ∀ j : Fin 5, (p j).edges.toFinset ∈ C := by
    intro j
    apply Finset.mem_filter.mpr
    constructor
    · apply (Basics.modCycleEdgeSets_finite 4 G).mem_toFinset.mpr
      apply (Basics.cycle_edges_mem_modCycleEdgeSets_iff (hp j)).mpr
      exact LayerFlux.follows_closed_length_dvd c π (by omega) (p j) (hf j)
    · exact LayerFlux.follows_cycle_good c π (by omega) (p j) (hp j) (hf j)
  have hcard : (Finset.univ : Finset (Fin 5)).card ≤ C.card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin 5 => (p j).edges.toFinset)
    · intro j _hj
      exact hmem j
    · intro a _ha b _hb hab
      exact hinj hab
  simpa only [C, Finset.card_univ, Fintype.card_fin] using hcard

end TaskH.GoodCycles

#print axioms TaskH.GoodCycles.good_mod_cycles_card_ge_five
