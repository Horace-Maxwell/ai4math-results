import Research.TaskH.Six.TraceSixPairs

/-!
Complete overlap classification of two different simple three-edge paths.
Classes 1 and 2 share an internal vertex in the same position.  Classes 3
and 4 have exactly one crossed overlap; class 5 has both crossed overlaps.
Class 0 is precisely an injective six-word and hence an actual hexagon.
The resulting identity is a finite path-pair identity.  Conversion of its
five bad-fibre cardinalities into degree moments is a separate obligation.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

noncomputable def tracePairClass (f : Fin 6 → V) : Fin 6 := by
  classical
  exact if f 1 = f 5 then 1 else if f 2 = f 4 then 2 else
    if f 1 = f 4 then (if f 2 = f 5 then 5 else 3) else
      if f 2 = f 5 then 4 else 0

theorem tracePairClass_classification (f : Fin 6 → V)
    (hf : IsTracePathPair G f) :
    (tracePairClass f = 0 ↔ Function.Injective f) ∧
      (tracePairClass f = 1 ↔ f 1 = f 5) ∧
      (tracePairClass f = 2 ↔ f 2 = f 4) ∧
      (tracePairClass f = 3 ↔ f 1 = f 4 ∧ f 2 ≠ f 5) ∧
      (tracePairClass f = 4 ↔ f 2 = f 5 ∧ f 1 ≠ f 4) ∧
      (tracePairClass f = 5 ↔ f 1 = f 4 ∧ f 2 = f 5) := by
  classical
  rcases (traceThreeWord_injective_iff (f 0) (f 1) (f 2) (f 3)).mp hf.1.1 with
    ⟨h01, h02, h03, h12, h13, h23⟩
  rcases (traceThreeWord_injective_iff (f 0) (f 5) (f 4) (f 3)).mp hf.2.1.1 with
    ⟨h05, h04, _, h54, h53, h43⟩
  have hn : ¬ (f 1 = f 5 ∧ f 2 = f 4) := by
    rintro ⟨h1, h2⟩
    exact hf.2.2 (Prod.ext h1 h2)
  rw [tracePathPair_injective_iff f hf]
  by_cases h15 : f 1 = f 5 <;> by_cases h24 : f 2 = f 4 <;>
    by_cases h14 : f 1 = f 4 <;> by_cases h25 : f 2 = f 5 <;>
      simp_all [tracePairClass]

noncomputable def traceOverlapWords [Fintype V] (G : SimpleGraph V)
    (i : Fin 6) : Finset (Fin 6 → V) := by
  classical
  exact (tracePathPairWords G).filter (fun f => tracePairClass f = i)

theorem mem_traceOverlapWords_iff [Fintype V] (i : Fin 6) (f : Fin 6 → V) :
    f ∈ traceOverlapWords G i ↔ IsTracePathPair G f ∧ tracePairClass f = i := by
  classical
  simp [traceOverlapWords, mem_tracePathPairWords_iff]

theorem traceOverlapWords_disjoint [Fintype V] (i j : Fin 6) (hne : i ≠ j) :
    Disjoint (traceOverlapWords G i) (traceOverlapWords G j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro f hi hj
  have he1 := ((mem_traceOverlapWords_iff i f).mp hi).2
  have he2 := ((mem_traceOverlapWords_iff j f).mp hj).2
  exact hne (he1.symm.trans he2)

open scoped Classical in
theorem traceOverlapWords_zero [Fintype V] :
    traceOverlapWords G 0 = Finset.univ.filter (IsHexagon G) := by
  classical
  ext f
  constructor
  · intro h
    obtain ⟨hp, hc⟩ := (mem_traceOverlapWords_iff 0 f).mp h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, tracePathPair_isHexagon f hp
      ((tracePairClass_classification f hp).1.mp hc)⟩
  · intro h
    have hh := (Finset.mem_filter.mp h).2
    have hp := isHexagon_isTracePathPair f hh
    exact (mem_traceOverlapWords_iff 0 f).mpr
      ⟨hp, (tracePairClass_classification f hp).1.mpr hh.1⟩

theorem traceOverlapWords_one_iff [Fintype V] (f : Fin 6 → V) :
    f ∈ traceOverlapWords G 1 ↔ IsTracePathPair G f ∧ f 1 = f 5 := by
  rw [mem_traceOverlapWords_iff]
  exact and_congr_right (fun hp => (tracePairClass_classification f hp).2.1)

theorem traceOverlapWords_two_iff [Fintype V] (f : Fin 6 → V) :
    f ∈ traceOverlapWords G 2 ↔ IsTracePathPair G f ∧ f 2 = f 4 := by
  rw [mem_traceOverlapWords_iff]
  exact and_congr_right (fun hp => (tracePairClass_classification f hp).2.2.1)

theorem traceOverlapWords_three_iff [Fintype V] (f : Fin 6 → V) :
    f ∈ traceOverlapWords G 3 ↔
      IsTracePathPair G f ∧ f 1 = f 4 ∧ f 2 ≠ f 5 := by
  rw [mem_traceOverlapWords_iff]
  exact and_congr_right (fun hp => (tracePairClass_classification f hp).2.2.2.1)

theorem traceOverlapWords_four_iff [Fintype V] (f : Fin 6 → V) :
    f ∈ traceOverlapWords G 4 ↔
      IsTracePathPair G f ∧ f 2 = f 5 ∧ f 1 ≠ f 4 := by
  rw [mem_traceOverlapWords_iff]
  exact and_congr_right (fun hp => (tracePairClass_classification f hp).2.2.2.2.1)

theorem traceOverlapWords_five_iff [Fintype V] (f : Fin 6 → V) :
    f ∈ traceOverlapWords G 5 ↔
      IsTracePathPair G f ∧ f 1 = f 4 ∧ f 2 = f 5 := by
  rw [mem_traceOverlapWords_iff]
  exact and_congr_right (fun hp => (tracePairClass_classification f hp).2.2.2.2.2)

theorem tracePathPairWords_card_sum_overlaps [Fintype V] :
    (tracePathPairWords G).card = ∑ i : Fin 6, (traceOverlapWords G i).card := by
  classical
  exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

open scoped Classical in
theorem tracePathPairWords_card_split [Fintype V] :
    (tracePathPairWords G).card =
      (Finset.univ.filter (IsHexagon G)).card +
        (traceOverlapWords G 1).card + (traceOverlapWords G 2).card +
          (traceOverlapWords G 3).card + (traceOverlapWords G 4).card +
            (traceOverlapWords G 5).card := by
  classical
  have hc := tracePathPairWords_card_sum_overlaps (G := G)
  simpa [Fin.sum_univ_succ, traceOverlapWords_zero, Nat.add_assoc] using hc

open scoped Classical in
theorem trace_three_path_pair_count_identity [Fintype V] :
    (Finset.univ.filter (IsHexagon G)).card +
        (traceOverlapWords G 1).card + (traceOverlapWords G 2).card +
          (traceOverlapWords G 3).card + (traceOverlapWords G 4).card +
            (traceOverlapWords G 5).card =
      ∑ u : V, ∑ v : V,
        ((traceThreePaths G u v).card ^ 2 - (traceThreePaths G u v).card) := by
  rw [← tracePathPairWords_card_split, tracePathPairWords_card]

end TaskH.Six

#print axioms TaskH.Six.tracePairClass_classification
#print axioms TaskH.Six.mem_traceOverlapWords_iff
#print axioms TaskH.Six.traceOverlapWords_disjoint
#print axioms TaskH.Six.traceOverlapWords_zero
#print axioms TaskH.Six.traceOverlapWords_one_iff
#print axioms TaskH.Six.traceOverlapWords_two_iff
#print axioms TaskH.Six.traceOverlapWords_three_iff
#print axioms TaskH.Six.traceOverlapWords_four_iff
#print axioms TaskH.Six.traceOverlapWords_five_iff
#print axioms TaskH.Six.tracePathPairWords_card_sum_overlaps
#print axioms TaskH.Six.tracePathPairWords_card_split
#print axioms TaskH.Six.trace_three_path_pair_count_identity
