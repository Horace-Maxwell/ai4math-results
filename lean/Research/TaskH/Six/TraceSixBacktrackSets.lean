import Research.TaskH.Six.TraceSixPaths

/-!
Three-edge walks and their two actual backtracking subsets.  For different
endpoints, removing `a=v` and `b=u` from `u-a-b-v` leaves exactly the actual
simple three-edge paths already used in the path-pair classification.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def IsTraceThreeWalk (G : SimpleGraph V) (u v : V) (p : V × V) : Prop :=
  G.Adj u p.1 ∧ G.Adj p.1 p.2 ∧ G.Adj p.2 v

theorem traceThreePath_iff_walk_no_backtrack (u v : V) (huv : u ≠ v) (p : V × V) :
    IsTraceThreePath G u v p ↔
      IsTraceThreeWalk G u v p ∧ p.1 ≠ v ∧ p.2 ≠ u := by
  constructor
  · intro hp
    have hn := (traceThreeWord_injective_iff u p.1 p.2 v).mp hp.1
    exact ⟨hp.2, hn.2.2.2.2.1, hn.2.1.symm⟩
  · rintro ⟨hw, hav, hbu⟩
    refine ⟨(traceThreeWord_injective_iff u p.1 p.2 v).mpr ?_, hw⟩
    exact ⟨hw.1.ne, hbu.symm, huv, hw.2.1.ne, hav, hw.2.2.ne⟩

variable [Fintype V]

noncomputable def traceThreeWalkPairs (G : SimpleGraph V) (u v : V) :
    Finset (V × V) := by
  classical
  exact Finset.univ.filter (IsTraceThreeWalk G u v)

noncomputable def traceEarlyBacktracks (G : SimpleGraph V) (u v : V) :
    Finset (V × V) := by
  classical
  exact (traceThreeWalkPairs G u v).filter (fun p => p.1 = v)

noncomputable def traceLateBacktracks (G : SimpleGraph V) (u v : V) :
    Finset (V × V) := by
  classical
  exact (traceThreeWalkPairs G u v).filter (fun p => p.2 = u)

theorem mem_traceThreeWalkPairs_iff (u v : V) (p : V × V) :
    p ∈ traceThreeWalkPairs G u v ↔ IsTraceThreeWalk G u v p := by
  classical
  simp [traceThreeWalkPairs]

theorem mem_traceEarlyBacktracks_iff (u v : V) (p : V × V) :
    p ∈ traceEarlyBacktracks G u v ↔ IsTraceThreeWalk G u v p ∧ p.1 = v := by
  classical
  simp [traceEarlyBacktracks, mem_traceThreeWalkPairs_iff]

theorem mem_traceLateBacktracks_iff (u v : V) (p : V × V) :
    p ∈ traceLateBacktracks G u v ↔ IsTraceThreeWalk G u v p ∧ p.2 = u := by
  classical
  simp [traceLateBacktracks, mem_traceThreeWalkPairs_iff]

open scoped Classical in
theorem traceThreePaths_eq_walkPairs_sdiff (u v : V) (huv : u ≠ v) :
    traceThreePaths G u v = traceThreeWalkPairs G u v \
      (traceEarlyBacktracks G u v ∪ traceLateBacktracks G u v) := by
  ext p
  simp only [mem_traceThreePaths_iff, Finset.mem_sdiff, Finset.mem_union,
    mem_traceThreeWalkPairs_iff, mem_traceEarlyBacktracks_iff,
    mem_traceLateBacktracks_iff, traceThreePath_iff_walk_no_backtrack u v huv]
  tauto

open scoped Classical in
theorem traceBacktracks_union_subset (u v : V) :
    traceEarlyBacktracks G u v ∪ traceLateBacktracks G u v ⊆
      traceThreeWalkPairs G u v := by
  classical
  intro p hp
  rcases Finset.mem_union.mp hp with he | hl
  · exact (mem_traceThreeWalkPairs_iff u v p).mpr
      ((mem_traceEarlyBacktracks_iff u v p).mp he).1
  · exact (mem_traceThreeWalkPairs_iff u v p).mpr
      ((mem_traceLateBacktracks_iff u v p).mp hl).1

open scoped Classical in
theorem traceThreeWalkPairs_card_inclusion_exclusion (u v : V) (huv : u ≠ v) :
    (traceThreeWalkPairs G u v).card +
        (traceEarlyBacktracks G u v ∩ traceLateBacktracks G u v).card =
      (traceThreePaths G u v).card + (traceEarlyBacktracks G u v).card +
        (traceLateBacktracks G u v).card := by
  classical
  have hp : (traceThreePaths G u v).card +
      (traceEarlyBacktracks G u v ∪ traceLateBacktracks G u v).card =
      (traceThreeWalkPairs G u v).card := by
    rw [traceThreePaths_eq_walkPairs_sdiff u v huv]
    exact Finset.card_sdiff_add_card_eq_card (traceBacktracks_union_subset u v)
  have hu := Finset.card_union_add_card_inter
    (traceEarlyBacktracks G u v) (traceLateBacktracks G u v)
  omega

variable [DecidableRel G.Adj]

theorem traceEarlyBacktracks_card (u v : V) :
    (traceEarlyBacktracks G u v).card = if G.Adj u v then G.degree v else 0 := by
  classical
  by_cases huv : G.Adj u v
  · rw [ite_eq_left huv, ← G.card_neighborFinset_eq_degree v]
    apply Finset.card_bij (fun p _ => p.2)
    · intro p hp
      obtain ⟨hw, he⟩ := (mem_traceEarlyBacktracks_iff u v p).mp hp
      apply (G.mem_neighborFinset v p.2).mpr
      simpa only [he] using hw.2.1
    · intro p hp q hq he
      have hpv := ((mem_traceEarlyBacktracks_iff u v p).mp hp).2
      have hqv := ((mem_traceEarlyBacktracks_iff u v q).mp hq).2
      exact Prod.ext (hpv.trans hqv.symm) he
    · intro b hb
      have hvb := (G.mem_neighborFinset v b).mp hb
      exact ⟨(v, b), (mem_traceEarlyBacktracks_iff u v (v, b)).mpr
        ⟨⟨huv, hvb, hvb.symm⟩, rfl⟩, rfl⟩
  · rw [ite_eq_right huv]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hw, he⟩ := (mem_traceEarlyBacktracks_iff u v p).mp hp
    exact huv (by simpa only [he] using hw.1)

theorem traceLateBacktracks_card (u v : V) :
    (traceLateBacktracks G u v).card = if G.Adj u v then G.degree u else 0 := by
  classical
  by_cases huv : G.Adj u v
  · rw [ite_eq_left huv, ← G.card_neighborFinset_eq_degree u]
    apply Finset.card_bij (fun p _ => p.1)
    · intro p hp
      have hw := ((mem_traceLateBacktracks_iff u v p).mp hp).1
      exact (G.mem_neighborFinset u p.1).mpr hw.1
    · intro p hp q hq he
      have hpu := ((mem_traceLateBacktracks_iff u v p).mp hp).2
      have hqu := ((mem_traceLateBacktracks_iff u v q).mp hq).2
      exact Prod.ext he (hpu.trans hqu.symm)
    · intro a ha
      have hua := (G.mem_neighborFinset u a).mp ha
      exact ⟨(a, u), (mem_traceLateBacktracks_iff u v (a, u)).mpr
        ⟨⟨hua, hua.symm, huv⟩, rfl⟩, rfl⟩
  · rw [ite_eq_right huv]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hw, he⟩ := (mem_traceLateBacktracks_iff u v p).mp hp
    exact huv (by simpa only [he] using hw.2.2)

open scoped Classical in
theorem traceBacktracks_inter (u v : V) :
    traceEarlyBacktracks G u v ∩ traceLateBacktracks G u v =
      if G.Adj u v then {(v, u)} else ∅ := by
  classical
  by_cases huv : G.Adj u v
  · rw [ite_eq_left huv]
    ext p
    constructor
    · intro hp
      obtain ⟨he, hl⟩ := Finset.mem_inter.mp hp
      exact Finset.mem_singleton.mpr (Prod.ext
        ((mem_traceEarlyBacktracks_iff u v p).mp he).2
        ((mem_traceLateBacktracks_iff u v p).mp hl).2)
    · intro hp
      have he : p = (v, u) := Finset.mem_singleton.mp hp
      subst p
      exact Finset.mem_inter.mpr
        ⟨(mem_traceEarlyBacktracks_iff u v _).mpr ⟨⟨huv, huv.symm, huv⟩, rfl⟩,
          (mem_traceLateBacktracks_iff u v _).mpr ⟨⟨huv, huv.symm, huv⟩, rfl⟩⟩
  · rw [ite_eq_right huv]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have he := (Finset.mem_inter.mp hp).1
    obtain ⟨hw, h1⟩ := (mem_traceEarlyBacktracks_iff u v p).mp he
    exact huv (by simpa only [h1] using hw.1)

open scoped Classical in
theorem traceBacktracks_inter_card (u v : V) :
    (traceEarlyBacktracks G u v ∩ traceLateBacktracks G u v).card =
      if G.Adj u v then 1 else 0 := by
  classical
  rw [traceBacktracks_inter]
  by_cases huv : G.Adj u v
  · simp only [ite_eq_left huv, Finset.card_singleton]
  · simp only [ite_eq_right huv, Finset.card_empty]

end TaskH.Six

#print axioms TaskH.Six.traceThreePath_iff_walk_no_backtrack
#print axioms TaskH.Six.mem_traceThreeWalkPairs_iff
#print axioms TaskH.Six.mem_traceEarlyBacktracks_iff
#print axioms TaskH.Six.mem_traceLateBacktracks_iff
#print axioms TaskH.Six.traceThreePaths_eq_walkPairs_sdiff
#print axioms TaskH.Six.traceBacktracks_union_subset
#print axioms TaskH.Six.traceThreeWalkPairs_card_inclusion_exclusion
#print axioms TaskH.Six.traceEarlyBacktracks_card
#print axioms TaskH.Six.traceLateBacktracks_card
#print axioms TaskH.Six.traceBacktracks_inter
#print axioms TaskH.Six.traceBacktracks_inter_card
