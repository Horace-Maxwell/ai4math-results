import Research.TaskH.Six.TraceSixCommonNeighbors

/-!
Exact evaluation of the double-cross overlap.  The word `(u,a,b,v,a,b)`
is a double-cross pair precisely when `a-b` is an actual edge and `u,v`
are different actual common neighbors of that edge.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def traceDoubleCrossWord (u v a b : V) : Fin 6 → V := ![u, a, b, v, a, b]

theorem traceDoubleCrossWord_isPair {u v a b : V}
    (hab : G.Adj a b) (hau : G.Adj a u) (hbu : G.Adj b u)
    (hav : G.Adj a v) (hbv : G.Adj b v) (huv : u ≠ v) :
    IsTracePathPair G (traceDoubleCrossWord u v a b) := by
  refine ⟨⟨(traceThreeWord_injective_iff u a b v).mpr ?_,
    hau.symm, hab, hbv⟩,
    ⟨(traceThreeWord_injective_iff u b a v).mpr ?_, hbu.symm, hab.symm, hav⟩, ?_⟩
  · exact ⟨hau.ne.symm, hbu.ne.symm, huv, hab.ne, hav.ne, hbv.ne⟩
  · exact ⟨hbu.ne.symm, hau.ne.symm, huv, hab.ne.symm, hbv.ne, hav.ne⟩
  · intro he
    exact hab.ne (congrArg Prod.fst he)

theorem traceDoubleCrossWord_class {u v a b : V} (hab : G.Adj a b) :
    tracePairClass (traceDoubleCrossWord u v a b) = 5 := by
  classical
  simp [tracePairClass, traceDoubleCrossWord, hab.ne, hab.ne.symm]

variable [Fintype V] [DecidableRel G.Adj]

open scoped Classical in
theorem trace_double_cross_fiber_card (a b : V) :
    ((traceOverlapWords G 5).filter (fun f => (f 1, f 2) = (a, b))).card =
      if G.Adj a b then (traceCommonNeighbors G a b).offDiag.card else 0 := by
  classical
  by_cases hab : G.Adj a b
  · rw [ite_eq_left hab]
    apply Finset.card_bij (fun f _ => (f 0, f 3))
    · intro f hf
      obtain ⟨hfm, he⟩ := Finset.mem_filter.mp hf
      obtain ⟨hp, h14, h25⟩ := (traceOverlapWords_five_iff f).mp hfm
      have h1 : f 1 = a := congrArg Prod.fst he
      have h2 : f 2 = b := congrArg Prod.snd he
      have h4 : f 4 = a := h14.symm.trans h1
      have h5 : f 5 = b := h25.symm.trans h2
      apply Finset.mem_offDiag.mpr
      refine ⟨(mem_traceCommonNeighbors_iff a b (f 0)).mpr ⟨?_, ?_⟩,
        (mem_traceCommonNeighbors_iff a b (f 3)).mpr ⟨?_, ?_⟩, ?_⟩
      · simpa only [h1] using hp.1.2.1.symm
      · simpa only [h5] using hp.2.1.2.1.symm
      · simpa only [h4] using hp.2.1.2.2.2
      · simpa only [h2] using hp.1.2.2.2
      · exact ((traceThreeWord_injective_iff _ _ _ _).mp hp.1.1).2.2.1
    · intro f hf g hg he
      obtain ⟨hfm, hfe⟩ := Finset.mem_filter.mp hf
      obtain ⟨hgm, hge⟩ := Finset.mem_filter.mp hg
      obtain ⟨_, hf14, hf25⟩ := (traceOverlapWords_five_iff f).mp hfm
      obtain ⟨_, hg14, hg25⟩ := (traceOverlapWords_five_iff g).mp hgm
      have h0 : f 0 = g 0 := congrArg Prod.fst he
      have h3 : f 3 = g 3 := congrArg Prod.snd he
      have h1 : f 1 = g 1 := (congrArg Prod.fst hfe).trans
        (congrArg Prod.fst hge).symm
      have h2 : f 2 = g 2 := (congrArg Prod.snd hfe).trans
        (congrArg Prod.snd hge).symm
      have h4 : f 4 = g 4 := hf14.symm.trans (h1.trans hg14)
      have h5 : f 5 = g 5 := hf25.symm.trans (h2.trans hg25)
      funext i
      fin_cases i <;> assumption
    · intro q hq
      obtain ⟨hu, hv, huv⟩ := Finset.mem_offDiag.mp hq
      obtain ⟨hau, hbu⟩ := (mem_traceCommonNeighbors_iff a b q.1).mp hu
      obtain ⟨hav, hbv⟩ := (mem_traceCommonNeighbors_iff a b q.2).mp hv
      have hp := traceDoubleCrossWord_isPair hab hau hbu hav hbv huv
      have hc := traceDoubleCrossWord_class (u := q.1) (v := q.2) hab
      refine ⟨traceDoubleCrossWord q.1 q.2 a b, Finset.mem_filter.mpr
        ⟨(mem_traceOverlapWords_iff 5 _).mpr ⟨hp, hc⟩, rfl⟩, rfl⟩
  · rw [ite_eq_right hab]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨hfm, he⟩ := Finset.mem_filter.mp hf
    have hp := ((traceOverlapWords_five_iff f).mp hfm).1
    have h1 : f 1 = a := congrArg Prod.fst he
    have h2 : f 2 = b := congrArg Prod.snd he
    exact hab (by simpa only [h1, h2] using hp.1.2.2.1)

theorem trace_double_cross_card :
    (traceOverlapWords G 5).card = 2 * traceOrientedDiamondPairs G := by
  classical
  calc
    _ = ∑ p : V × V,
        ((traceOverlapWords G 5).filter (fun f => (f 1, f 2) = p)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ = ∑ p : V × V,
        if G.Adj p.1 p.2 then (traceCommonNeighbors G p.1 p.2).offDiag.card else 0 :=
      Finset.sum_congr rfl (fun p _ => trace_double_cross_fiber_card p.1 p.2)
    _ = ∑ a : V, ∑ b : V,
        if G.Adj a b then (traceCommonNeighbors G a b).offDiag.card else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : V, ∑ b ∈ G.neighborFinset a,
        (traceCommonNeighbors G a b).offDiag.card := by
      apply Finset.sum_congr rfl
      intro a _
      have hn : (Finset.univ.filter (fun b => G.Adj a b)) = G.neighborFinset a := by
        ext b
        simp
      rw [← hn, Finset.sum_filter]
    _ = 2 * traceOrientedDiamondPairs G := by
      simp only [trace_offDiag_card_eq_two_choose, traceOrientedDiamondPairs, Finset.mul_sum]

end TaskH.Six

#print axioms TaskH.Six.traceDoubleCrossWord_isPair
#print axioms TaskH.Six.traceDoubleCrossWord_class
#print axioms TaskH.Six.trace_double_cross_fiber_card
#print axioms TaskH.Six.trace_double_cross_card
