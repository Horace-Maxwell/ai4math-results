import Research.TaskH.Five.LayerCycles
import Research.TaskH.Five.LayerFlux
import Research.TaskH.Five.LayerCycleSeparation

/-!
The actual six-good-cycles lower bound for each deleted-vertex coloring
and each color order. All six witnesses are genuine graph cycles; their
unoriented edge sets are injected into the frozen modulo-five cycle set.
-/

universe u

namespace TaskH.Five.GoodCycles

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {v : V}

open scoped Classical in
theorem good_mod_cycles_card_ge_six [Fintype V] (hnot : ¬ G.Colorable 5)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (π : Equiv.Perm (Fin 5)) :
    6 ≤ (((Basics.modCycleEdgeSets_finite 5 G).toFinset).filter
      (GoodCycleOrder c π)).card := by
  classical
  have hex : ∀ j : Fin 6, ∃ t : V,
      t ∈ LayerColoring.Ti c π j.val \ LayerColoring.Ti c π (j.val + 1) ∧
      ∃ p : G.Walk t t, p.IsCycle ∧
        Follows p (LayerColoring.shiftedColor c π (j.val + 1)) (finRotate 5) := by
    intro j
    have hj := j.isLt
    have hrange : 1 ≤ j.val + 1 ∧ j.val + 1 ≤ 6 := by omega
    obtain ⟨t, ht, p, hp, hf⟩ := LayerCycles.exists_layer_cycle c π hnot hrange
    refine ⟨t, ?_, p, hp, hf⟩
    simpa only [Nat.add_sub_cancel] using ht
  choose t ht p hp hf using hex
  have hanti : ∀ {a b : ℕ}, a ≤ b →
      LayerColoring.Ti c π b ⊆ LayerColoring.Ti c π a := by
    intro _a _b hab
    exact LayerSets.T_antitone hab
  have hfbit : ∀ j : Fin 6, Follows (p j)
      (fun z => shiftBit (LayerColoring.baseColor c π z)
        (decide (z ∈ LayerColoring.Ti c π (j.val + 1)))) (finRotate 5) := by
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
  have hinj : Function.Injective (fun j : Fin 6 => (p j).edges.toFinset) :=
    layer_cycle_edgeSets_injective (LayerColoring.baseColor c π)
      (LayerColoring.Ti c π) hanti t p hp hfbit ht
  let C : Finset (Finset (Sym2 V)) :=
    ((Basics.modCycleEdgeSets_finite 5 G).toFinset).filter (GoodCycleOrder c π)
  have hmem : ∀ j : Fin 6, (p j).edges.toFinset ∈ C := by
    intro j
    apply Finset.mem_filter.mpr
    constructor
    · apply (Basics.modCycleEdgeSets_finite 5 G).mem_toFinset.mpr
      apply (Basics.cycle_edges_mem_modCycleEdgeSets_iff (hp j)).mpr
      exact LayerFlux.follows_closed_length_dvd c π (by omega) (p j) (hf j)
    · exact LayerFlux.follows_cycle_good c π (by omega) (p j) (hp j) (hf j)
  have hcard : (Finset.univ : Finset (Fin 6)).card ≤ C.card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin 6 => (p j).edges.toFinset)
    · intro j _hj
      exact hmem j
    · intro a _ha b _hb hab
      exact hinj hab
  simpa only [C, Finset.card_univ, Fintype.card_fin] using hcard

end TaskH.Five.GoodCycles


#print axioms TaskH.Five.GoodCycles.good_mod_cycles_card_ge_six
