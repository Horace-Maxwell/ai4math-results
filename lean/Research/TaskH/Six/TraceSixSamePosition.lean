import Research.TaskH.Six.TraceSixSamePositionData

/-!
Exact same-position overlap evaluation in the original graph.  Each fixed
ordered pair of different common neighbors admits exactly the original
neighbors of `a` outside `{v,b,d}` as its roots.  Both orientations of the
shared internal position are counted using the actual word reversal.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem traceSamePositionFiber_commonPair (a v : V) (f : Fin 6 → V)
    (hf : f ∈ traceSamePositionFiber G a v) :
    (f 2, f 4) ∈ (traceCommonNeighbors G a v).offDiag := by
  obtain ⟨hfm, he⟩ := (mem_traceSamePositionFiber_iff a v f).mp hf
  obtain ⟨hp, h15⟩ := (traceOverlapWords_one_iff f).mp hfm
  have h1 : f 1 = a := congrArg Prod.fst he
  have h3 : f 3 = v := congrArg Prod.snd he
  have h5 : f 5 = a := h15.symm.trans h1
  apply Finset.mem_offDiag.mpr
  refine ⟨(mem_traceCommonNeighbors_iff a v (f 2)).mpr ⟨?_, ?_⟩,
    (mem_traceCommonNeighbors_iff a v (f 4)).mpr ⟨?_, ?_⟩, ?_⟩
  · simpa only [h1] using hp.1.2.2.1
  · simpa only [h3] using hp.1.2.2.2.symm
  · simpa only [h5] using hp.2.1.2.2.1
  · simpa only [h3] using hp.2.1.2.2.2.symm
  · intro he24
    exact hp.2.2 (Prod.ext h15 he24)

open scoped Classical in
theorem trace_same_position_subfiber_card (a v b d : V) (hav : a ≠ v)
    (hq : (b, d) ∈ (traceCommonNeighbors G a v).offDiag) :
    ((traceSamePositionFiber G a v).filter (fun f => (f 2, f 4) = (b, d))).card =
      G.degree a - 2 - (if G.Adj a v then 1 else 0) := by
  classical
  calc
    _ = (traceSamePositionRoots G a v b d).card := by
      apply Finset.card_bij (fun f _ => f 0)
      · intro f hf
        obtain ⟨hbase, he24⟩ := Finset.mem_filter.mp hf
        obtain ⟨hfm, he13⟩ := (mem_traceSamePositionFiber_iff a v f).mp hbase
        have hp := ((traceOverlapWords_one_iff f).mp hfm).1
        have h1 : f 1 = a := congrArg Prod.fst he13
        have h3 : f 3 = v := congrArg Prod.snd he13
        have h2 : f 2 = b := congrArg Prod.fst he24
        have h4 : f 4 = d := congrArg Prod.snd he24
        have hn1 := (traceThreeWord_injective_iff _ _ _ _).mp hp.1.1
        have hn2 := (traceThreeWord_injective_iff _ _ _ _).mp hp.2.1.1
        apply (mem_traceSamePositionRoots_iff a v b d (f 0)).mpr
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa only [h1] using hp.1.2.1.symm
        · simpa only [h3] using hn1.2.2.1
        · simpa only [h2] using hn1.2.1
        · simpa only [h4] using hn2.2.1
      · intro f hf g hg he0
        obtain ⟨hfb, hfe24⟩ := Finset.mem_filter.mp hf
        obtain ⟨hgb, hge24⟩ := Finset.mem_filter.mp hg
        obtain ⟨hfm, hfe13⟩ := (mem_traceSamePositionFiber_iff a v f).mp hfb
        obtain ⟨hgm, hge13⟩ := (mem_traceSamePositionFiber_iff a v g).mp hgb
        have hf15 := ((traceOverlapWords_one_iff f).mp hfm).2
        have hg15 := ((traceOverlapWords_one_iff g).mp hgm).2
        have h1 : f 1 = g 1 := (congrArg Prod.fst hfe13).trans
          (congrArg Prod.fst hge13).symm
        have h3 : f 3 = g 3 := (congrArg Prod.snd hfe13).trans
          (congrArg Prod.snd hge13).symm
        have h2 : f 2 = g 2 := (congrArg Prod.fst hfe24).trans
          (congrArg Prod.fst hge24).symm
        have h4 : f 4 = g 4 := (congrArg Prod.snd hfe24).trans
          (congrArg Prod.snd hge24).symm
        have h5 : f 5 = g 5 := hf15.symm.trans (h1.trans hg15)
        funext i
        fin_cases i <;> assumption
      · intro u hu
        have hm := traceSamePositionWord_mem_one a v b d u hav hq hu
        exact ⟨traceSamePositionWord u a b v d,
          Finset.mem_filter.mpr ⟨(mem_traceSamePositionFiber_iff a v _).mpr
            ⟨hm, rfl⟩, rfl⟩, rfl⟩
    _ = _ := traceSamePositionRoots_card a v b d hq

open scoped Classical in
theorem traceSamePositionFiber_card (a v : V) :
    (traceSamePositionFiber G a v).card = if a ≠ v then
      (traceCommonNeighbors G a v).offDiag.card *
        (G.degree a - 2 - (if G.Adj a v then 1 else 0)) else 0 := by
  classical
  by_cases hav : a ≠ v
  · rw [ite_eq_left hav]
    calc
      _ = ∑ q ∈ (traceCommonNeighbors G a v).offDiag,
          ((traceSamePositionFiber G a v).filter (fun f => (f 2, f 4) = q)).card :=
        Finset.card_eq_sum_card_fiberwise (fun f hf =>
          traceSamePositionFiber_commonPair a v f hf)
      _ = ∑ _q ∈ (traceCommonNeighbors G a v).offDiag,
          (G.degree a - 2 - (if G.Adj a v then 1 else 0)) :=
        Finset.sum_congr rfl (fun q hq =>
          trace_same_position_subfiber_card a v q.1 q.2 hav hq)
      _ = _ := by simp
  · have he : a = v := not_ne_iff.mp hav
    subst v
    rw [traceSamePositionFiber_self]
    simp

theorem trace_same_position_one_card :
    (traceOverlapWords G 1).card = 2 * traceSamePositionBudget G := by
  classical
  calc
    _ = ∑ p : V × V,
        ((traceOverlapWords G 1).filter (fun f => (f 1, f 3) = p)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ = ∑ p : V × V, (traceSamePositionFiber G p.1 p.2).card := rfl
    _ = ∑ a : V, ∑ v : V, if a ≠ v then
        (traceCommonNeighbors G a v).offDiag.card *
          (G.degree a - 2 - (if G.Adj a v then 1 else 0)) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_congr rfl (fun v _ => traceSamePositionFiber_card a v)
    _ = 2 * traceSamePositionBudget G := by
      unfold traceSamePositionBudget
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hav : a ≠ v
      · simp only [ite_eq_left hav, trace_offDiag_card_eq_two_choose]
        ring
      · simp only [ite_eq_right hav, mul_zero]

theorem trace_same_position_total_card :
    (traceOverlapWords G 1).card + (traceOverlapWords G 2).card =
      4 * traceSamePositionBudget G := by
  have h1 := trace_same_position_one_card (G := G)
  have h2 := trace_overlap_one_card_eq_two (G := G)
  omega

end TaskH.Six

#print axioms TaskH.Six.traceSamePositionFiber_commonPair
#print axioms TaskH.Six.trace_same_position_subfiber_card
#print axioms TaskH.Six.traceSamePositionFiber_card
#print axioms TaskH.Six.trace_same_position_one_card
#print axioms TaskH.Six.trace_same_position_total_card
