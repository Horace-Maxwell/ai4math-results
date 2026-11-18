import Research.TaskH.General.LayerCycles
import Research.TaskH.General.LayerFlux
import Research.TaskH.General.LayerCycleSeparation
import Research.TaskH.General.EqualityShortCycles

/-!
The actual k+1 good-cycles lower bound for each deleted-vertex coloring
and each color order. All k+1 witnesses are genuine graph cycles; their
unoriented edge sets are injected into the frozen modulo-k cycle set.
-/

universe u

namespace TaskH.General.GoodCycles

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {v : V} {k : ℕ}

open scoped Classical in
theorem good_mod_cycles_card_ge_succ [Fintype V] (hk : 4 ≤ k) (hnot : ¬ G.Colorable k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (π : Equiv.Perm (Fin k)) :
    k + 1 ≤ (((Basics.modCycleEdgeSets_finite k G).toFinset).filter
      (GoodCycleOrder c π)).card := by
  classical
  have hex : ∀ j : Fin (k + 1), ∃ t : V,
      t ∈ LayerColoring.Ti (by omega : 3 ≤ k) c π j.val \ LayerColoring.Ti (by omega : 3 ≤ k) c π (j.val + 1) ∧
      ∃ p : G.Walk t t, p.IsCycle ∧
        Follows p (LayerColoring.shiftedColor (by omega : 3 ≤ k) c π (j.val + 1)) (finRotate k) := by
    intro j
    have hj := j.isLt
    have hrange : 1 ≤ j.val + 1 ∧ j.val + 1 ≤ k + 1 := by omega
    obtain ⟨t, ht, p, hp, hf⟩ := LayerCycles.exists_layer_cycle (by omega : 3 ≤ k) c π hnot hrange
    refine ⟨t, ?_, p, hp, hf⟩
    simpa only [Nat.add_sub_cancel] using ht
  choose t ht p hp hf using hex
  have hanti : ∀ {a b : ℕ}, a ≤ b →
      LayerColoring.Ti (by omega : 3 ≤ k) c π b ⊆ LayerColoring.Ti (by omega : 3 ≤ k) c π a := by
    intro _a _b hab
    exact LayerSets.T_antitone hab
  have hfbit : ∀ j : Fin (k + 1), Follows (p j)
      (fun z => shiftBit (LayerColoring.baseColor (by omega : 3 ≤ k) c π z)
        (decide (z ∈ LayerColoring.Ti (by omega : 3 ≤ k) c π (j.val + 1)))) (finRotate k) := by
    intro j
    have hfun : LayerColoring.shiftedColor (by omega : 3 ≤ k) c π (j.val + 1) =
        (fun z => shiftBit (LayerColoring.baseColor (by omega : 3 ≤ k) c π z)
          (decide (z ∈ LayerColoring.Ti (by omega : 3 ≤ k) c π (j.val + 1)))) := by
      funext z
      rw [LayerFlux.shiftedColor_eq_shiftBit]
      by_cases hz : z ∈ LayerColoring.Ti (by omega : 3 ≤ k) c π (j.val + 1) <;>
        simp [LayerFlux.shiftFlag, hz]
    rw [← hfun]
    exact hf j
  have hinj : Function.Injective (fun j : Fin (k + 1) => (p j).edges.toFinset) :=
    layer_cycle_edgeSets_injective hk (LayerColoring.baseColor (by omega : 3 ≤ k) c π)
      (LayerColoring.Ti (by omega : 3 ≤ k) c π) hanti t p hp hfbit ht
  let C : Finset (Finset (Sym2 V)) :=
    ((Basics.modCycleEdgeSets_finite k G).toFinset).filter (GoodCycleOrder c π)
  have hmem : ∀ j : Fin (k + 1), (p j).edges.toFinset ∈ C := by
    intro j
    apply Finset.mem_filter.mpr
    constructor
    · apply (Basics.modCycleEdgeSets_finite k G).mem_toFinset.mpr
      apply (Basics.cycle_edges_mem_modCycleEdgeSets_iff (hp j)).mpr
      exact LayerFlux.follows_closed_length_dvd (by omega : 3 ≤ k) c π (by omega) (p j) (hf j)
    · exact LayerFlux.follows_cycle_good (by omega : 3 ≤ k) c π (by omega) (p j) (hp j) (hf j)
  have hcard : (Finset.univ : Finset (Fin (k + 1))).card ≤ C.card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin (k + 1) => (p j).edges.toFinset)
    · intro j _hj
      exact hmem j
    · intro a _ha b _hb hab
      exact hinj hab
  simpa only [C, Finset.card_univ, Fintype.card_fin] using hcard

/-- The original critical graph supplies the actual per-order R lower bound. -/
theorem actual_good_cycle_lower_bound [Fintype V] (hk : 4 ≤ k)
    (hcrit : Challenge.IsCriticalPlus k G) : TaskH.General.ActualGoodCycleLowerBound k G := by
  classical
  intro v c π
  exact good_mod_cycles_card_ge_succ hk (critical_not_colorable hcrit) c π

/-- The original criticality and original equality now discharge the old
conditional S interface, without an extra lower-bound premise. -/
theorem equality_shortCycles_from_critical_count [Fintype V] (hk : 4 ≤ k)
    (hcrit : Challenge.IsCriticalPlus k G)
    (hcount : Challenge.modCycleCount k G = Challenge.bound k) :
    TaskH.General.ShortCycles k G := by
  exact TaskH.General.equality_shortCycles_of_actual_lower_bound
    (by omega : 3 ≤ k) hcrit hcount (actual_good_cycle_lower_bound hk hcrit)

end TaskH.General.GoodCycles


#print axioms TaskH.General.GoodCycles.good_mod_cycles_card_ge_succ

#print axioms TaskH.General.GoodCycles.actual_good_cycle_lower_bound

#print axioms TaskH.General.GoodCycles.equality_shortCycles_from_critical_count
