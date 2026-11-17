import Research.TaskH.Six.TraceSixEdgePairCounts
import Research.TaskH.Six.TraceSixPairReversal
import Research.TaskH.Six.TraceSixCommonNeighbors
import Research.TaskH.Six.TraceSixMantel

/-!
Actual single-cross pairs at `a` are `(u,a,b,v,a,c)`.  The four other
vertices form the actual two disjoint oriented edges `(u,c)` and `(b,v)`
inside the induced neighborhood graph of `a`.  Both directions of this
correspondence are constructed below, with no neighborhood-count premise.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def traceSingleCrossIndex : Fin 4 → Fin 6 := ![0, 5, 2, 3]

def traceSingleCrossFromNeighborWord (a : V) (q : Fin 4 → G.neighborSet a) :
    Fin 6 → V := ![(q 0 : V), a, (q 2 : V), (q 3 : V), a, (q 1 : V)]

variable [Fintype V]

noncomputable def traceSingleCrossFiber (G : SimpleGraph V) (a : V) :
    Finset (Fin 6 → V) := by
  classical
  exact (traceOverlapWords G 3).filter (fun f => f 1 = a)

theorem mem_traceSingleCrossFiber_iff (a : V) (f : Fin 6 → V) :
    f ∈ traceSingleCrossFiber G a ↔ f ∈ traceOverlapWords G 3 ∧ f 1 = a := by
  classical
  simp [traceSingleCrossFiber]

theorem traceSingleCross_neighbor (a : V) (f : Fin 6 → V)
    (hf : f ∈ traceSingleCrossFiber G a) (i : Fin 4) :
    G.Adj a (f (traceSingleCrossIndex i)) := by
  obtain ⟨hfm, h1⟩ := (mem_traceSingleCrossFiber_iff a f).mp hf
  obtain ⟨hp, h14, _⟩ := (traceOverlapWords_three_iff f).mp hfm
  have h4 : f 4 = a := h14.symm.trans h1
  fin_cases i
  · change G.Adj a (f 0)
    simpa only [h1] using hp.1.2.1.symm
  · change G.Adj a (f 5)
    simpa only [h4] using hp.2.1.2.2.1.symm
  · change G.Adj a (f 2)
    simpa only [h1] using hp.1.2.2.1
  · change G.Adj a (f 3)
    simpa only [h4] using hp.2.1.2.2.2

def traceSingleCrossVertices (a : V) (f : Fin 6 → V)
    (hf : f ∈ traceSingleCrossFiber G a) : Fin 4 → G.neighborSet a :=
  fun i => ⟨f (traceSingleCrossIndex i), traceSingleCross_neighbor a f hf i⟩

variable [DecidableRel G.Adj]

theorem traceSingleCrossVertices_mem_disjoint (a : V) (f : Fin 6 → V)
    (hf : f ∈ traceSingleCrossFiber G a) :
    traceSingleCrossVertices a f hf ∈ traceDisjointEdgeWords (G.induce (G.neighborSet a)) := by
  obtain ⟨hfm, _⟩ := (mem_traceSingleCrossFiber_iff a f).mp hf
  obtain ⟨hp, _, h25⟩ := (traceOverlapWords_three_iff f).mp hfm
  apply (mem_traceDisjointEdgeWords_iff _).mpr
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change G.Adj (f 0) (f 5)
    exact hp.2.1.2.1
  · change G.Adj (f 2) (f 3)
    exact hp.1.2.2.2
  · obtain ⟨h01, h02, h03, h12, h13, h23⟩ :=
      (traceThreeWord_injective_iff _ _ _ _).mp hp.1.1
    obtain ⟨h05, h04, _, h54, h53, h43⟩ :=
      (traceThreeWord_injective_iff _ _ _ _).mp hp.2.1.1
    intro i j hij
    have hv := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;>
      simp_all [traceSingleCrossVertices, traceSingleCrossIndex]

theorem traceSingleCrossFromNeighborWord_mem (a : V)
    (q : Fin 4 → G.neighborSet a)
    (hq : q ∈ traceDisjointEdgeWords (G.induce (G.neighborSet a))) :
    traceSingleCrossFromNeighborWord a q ∈ traceSingleCrossFiber G a := by
  obtain ⟨he, hi⟩ := (mem_traceDisjointEdgeWords_iff q).mp hq
  have hival : Function.Injective (fun i => (q i : V)) := Subtype.val_injective.comp hi
  have hn : ∀ {i j : Fin 4}, i ≠ j → (q i : V) ≠ (q j : V) := hival.ne
  have hp : IsTracePathPair G (traceSingleCrossFromNeighborWord a q) := by
    refine ⟨⟨(traceThreeWord_injective_iff (q 0 : V) a (q 2 : V) (q 3 : V)).mpr ?_,
      (q 0).property.symm, (q 2).property, he.2⟩,
      ⟨(traceThreeWord_injective_iff (q 0 : V) (q 1 : V) a (q 3 : V)).mpr ?_,
        he.1, (q 1).property.symm, (q 3).property⟩, ?_⟩
    · exact ⟨(q 0).property.ne.symm, hn (by decide : (0 : Fin 4) ≠ 2),
        hn (by decide : (0 : Fin 4) ≠ 3), (q 2).property.ne,
        (q 3).property.ne, hn (by decide : (2 : Fin 4) ≠ 3)⟩
    · exact ⟨hn (by decide : (0 : Fin 4) ≠ 1), (q 0).property.ne.symm,
        hn (by decide : (0 : Fin 4) ≠ 3), (q 1).property.ne.symm,
        hn (by decide : (1 : Fin 4) ≠ 3), (q 3).property.ne⟩
    · intro heq
      exact (q 1).property.ne (congrArg Prod.fst heq)
  apply (mem_traceSingleCrossFiber_iff a _).mpr
  exact ⟨(traceOverlapWords_three_iff _).mpr
    ⟨hp, rfl, hn (by decide : (2 : Fin 4) ≠ 1)⟩, rfl⟩

omit [DecidableRel G.Adj] in
theorem traceSingleCrossFromNeighborWord_vertices (a : V) (f : Fin 6 → V)
    (hf : f ∈ traceSingleCrossFiber G a) :
    traceSingleCrossFromNeighborWord a (traceSingleCrossVertices a f hf) = f := by
  obtain ⟨hfm, h1⟩ := (mem_traceSingleCrossFiber_iff a f).mp hf
  have h14 := ((traceOverlapWords_three_iff f).mp hfm).2.1
  have h4 : f 4 = a := h14.symm.trans h1
  funext i
  fin_cases i
  · rfl
  · exact h1.symm
  · rfl
  · rfl
  · exact h4.symm
  · rfl

theorem traceSingleCrossVertices_fromNeighborWord (a : V)
    (q : Fin 4 → G.neighborSet a)
    (hq : q ∈ traceDisjointEdgeWords (G.induce (G.neighborSet a))) :
    traceSingleCrossVertices a (traceSingleCrossFromNeighborWord a q)
      (traceSingleCrossFromNeighborWord_mem a q hq) = q := by
  funext i
  apply Subtype.ext
  fin_cases i <;> rfl

theorem trace_single_cross_fiber_card (a : V) :
    (traceSingleCrossFiber G a).card =
      (traceDisjointEdgeWords (G.induce (G.neighborSet a))).card := by
  classical
  apply Finset.card_bij (fun f hf => traceSingleCrossVertices a f hf)
  · intro f hf
    exact traceSingleCrossVertices_mem_disjoint a f hf
  · intro f hf g hg he
    have hh := congrArg (traceSingleCrossFromNeighborWord a) he
    simpa only [traceSingleCrossFromNeighborWord_vertices] using hh
  · intro q hq
    exact ⟨traceSingleCrossFromNeighborWord a q, traceSingleCrossFromNeighborWord_mem a q hq,
      traceSingleCrossVertices_fromNeighborWord a q hq⟩

theorem trace_neighbor_degree_eq_common_card (a : V) (x : G.neighborSet a) :
    (G.induce (G.neighborSet a)).degree x =
      (traceCommonNeighbors G a (x : V)).card := by
  classical
  rw [← (G.induce (G.neighborSet a)).card_neighborFinset_eq_degree x]
  apply Finset.card_bij (fun (z : G.neighborSet a) _ => z.val)
  · intro z hz
    have hxz := ((G.induce (G.neighborSet a)).mem_neighborFinset x z).mp hz
    exact (mem_traceCommonNeighbors_iff a (x : V) (z : V)).mpr ⟨z.property, hxz⟩
  · intro z _ w _ he
    exact Subtype.ext he
  · intro z hz
    obtain ⟨haz, hxz⟩ := (mem_traceCommonNeighbors_iff a (x : V) z).mp hz
    exact ⟨⟨z, haz⟩,
      ((G.induce (G.neighborSet a)).mem_neighborFinset x ⟨z, haz⟩).mpr hxz, rfl⟩

theorem trace_neighbor_common_square_sum (a : V) :
    (∑ x : G.neighborSet a, ((G.induce (G.neighborSet a)).degree x : ℝ) ^ 2) =
      ∑ x ∈ G.neighborFinset a, ((traceCommonNeighbors G a x).card : ℝ) ^ 2 := by
  classical
  calc
    _ = ∑ x : G.neighborSet a, ((traceCommonNeighbors G a (x : V)).card : ℝ) ^ 2 :=
      Finset.sum_congr rfl (fun x _ => by rw [trace_neighbor_degree_eq_common_card])
    _ = _ := (Finset.sum_subtype (G.neighborFinset a)
      (fun x => G.mem_neighborFinset a x)
      (fun x => ((traceCommonNeighbors G a x).card : ℝ) ^ 2)).symm

theorem trace_single_cross_fiber_card_real (a : V) :
    ((traceSingleCrossFiber G a).card : ℝ) =
      4 * (traceLocalTriangleCount G a : ℝ) ^ 2 +
        4 * traceLocalTriangleCount G a -
          4 * (∑ x ∈ G.neighborFinset a,
            ((traceCommonNeighbors G a x).card : ℝ) ^ 2) := by
  rw [trace_single_cross_fiber_card]
  have hh := trace_disjoint_edge_words_count_real (G := G.induce (G.neighborSet a))
  rw [trace_neighbor_common_square_sum] at hh
  simpa only [traceLocalTriangleCount] using hh

theorem trace_single_cross_three_card_real :
    ((traceOverlapWords G 3).card : ℝ) =
      4 * traceTriangleMoment G 2 + 4 * traceTriangleMoment G 1 -
        4 * (∑ a : V, ∑ x ∈ G.neighborFinset a,
          ((traceCommonNeighbors G a x).card : ℝ) ^ 2) := by
  classical
  have hn : (traceOverlapWords G 3).card =
      ∑ a : V, (traceSingleCrossFiber G a).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  calc
    _ = ∑ a : V, ((traceSingleCrossFiber G a).card : ℝ) := by exact_mod_cast hn
    _ = ∑ a : V, (4 * (traceLocalTriangleCount G a : ℝ) ^ 2 +
        4 * traceLocalTriangleCount G a -
          4 * (∑ x ∈ G.neighborFinset a,
            ((traceCommonNeighbors G a x).card : ℝ) ^ 2)) :=
      Finset.sum_congr rfl (fun a _ => trace_single_cross_fiber_card_real a)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, traceTriangleMoment, pow_one]

theorem trace_single_cross_total_card_real :
    ((traceOverlapWords G 3).card : ℝ) + (traceOverlapWords G 4).card =
      8 * traceTriangleMoment G 2 + 8 * traceTriangleMoment G 1 -
        8 * (∑ a : V, ∑ x ∈ G.neighborFinset a,
          ((traceCommonNeighbors G a x).card : ℝ) ^ 2) := by
  have h3 := trace_single_cross_three_card_real (G := G)
  have h4 : ((traceOverlapWords G 3).card : ℝ) = (traceOverlapWords G 4).card := by
    exact_mod_cast (trace_overlap_three_card_eq_four (G := G))
  linarith

end TaskH.Six

#print axioms TaskH.Six.mem_traceSingleCrossFiber_iff
#print axioms TaskH.Six.traceSingleCross_neighbor
#print axioms TaskH.Six.traceSingleCrossVertices_mem_disjoint
#print axioms TaskH.Six.traceSingleCrossFromNeighborWord_mem
#print axioms TaskH.Six.traceSingleCrossFromNeighborWord_vertices
#print axioms TaskH.Six.traceSingleCrossVertices_fromNeighborWord
#print axioms TaskH.Six.trace_single_cross_fiber_card
#print axioms TaskH.Six.trace_neighbor_degree_eq_common_card
#print axioms TaskH.Six.trace_neighbor_common_square_sum
#print axioms TaskH.Six.trace_single_cross_fiber_card_real
#print axioms TaskH.Six.trace_single_cross_three_card_real
#print axioms TaskH.Six.trace_single_cross_total_card_real
