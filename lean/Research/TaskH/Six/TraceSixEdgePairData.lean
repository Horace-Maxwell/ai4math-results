import Research.TaskH.Six.TraceSixPaths

/-!
Actual ordered pairs of oriented edges, represented by four original
vertices.  The full endpoint-overlap correction is pointwise and uses only
looplessness.  No edge or degree count is postulated as a graph premise.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def IsTraceEdgePair (G : SimpleGraph V) (f : Fin 4 → V) : Prop :=
  G.Adj (f 0) (f 1) ∧ G.Adj (f 2) (f 3)

def traceEdgePairReindex (left right : Bool) (f : Fin 4 → V) : Fin 4 → V :=
  ![if left then f 1 else f 0, if left then f 0 else f 1,
    if right then f 3 else f 2, if right then f 2 else f 3]

def TraceEdgePairCross (left right : Bool) (f : Fin 4 → V) : Prop :=
  traceEdgePairReindex left right f 0 = traceEdgePairReindex left right f 2

def TraceEdgePairDiagonal (reverse : Bool) (f : Fin 4 → V) : Prop :=
  traceEdgePairReindex false reverse f 0 = traceEdgePairReindex false reverse f 2 ∧
    traceEdgePairReindex false reverse f 1 = traceEdgePairReindex false reverse f 3

theorem traceEdgePairReindex_involutive (left right : Bool) (f : Fin 4 → V) :
    traceEdgePairReindex left right (traceEdgePairReindex left right f) = f := by
  cases left <;> cases right <;> funext i <;> fin_cases i <;> rfl

theorem traceEdgePairReindex_isPair (left right : Bool) (f : Fin 4 → V)
    (hf : IsTraceEdgePair G f) : IsTraceEdgePair G (traceEdgePairReindex left right f) := by
  cases left <;> cases right
  · exact hf
  · exact ⟨hf.1, hf.2.symm⟩
  · exact ⟨hf.1.symm, hf.2⟩
  · exact ⟨hf.1.symm, hf.2.symm⟩

theorem traceEdgePair_injective_iff (f : Fin 4 → V) (hf : IsTraceEdgePair G f) :
    Function.Injective f ↔
      f 0 ≠ f 2 ∧ f 0 ≠ f 3 ∧ f 1 ≠ f 2 ∧ f 1 ≠ f 3 := by
  constructor
  · intro h
    exact ⟨h.ne (by decide : (0 : Fin 4) ≠ 2),
      h.ne (by decide : (0 : Fin 4) ≠ 3),
      h.ne (by decide : (1 : Fin 4) ≠ 2),
      h.ne (by decide : (1 : Fin 4) ≠ 3)⟩
  · rintro ⟨h02, h03, h12, h13⟩ i j hij
    have h01 := hf.1.ne
    have h23 := hf.2.ne
    fin_cases i <;> fin_cases j <;> simp_all

open scoped Classical in
theorem traceEdgePair_indicator_balance (f : Fin 4 → V) (hf : IsTraceEdgePair G f) :
    1 + (if TraceEdgePairDiagonal false f then 1 else 0) +
        (if TraceEdgePairDiagonal true f then 1 else 0) =
      (if Function.Injective f then 1 else 0) +
        (if TraceEdgePairCross false false f then 1 else 0) +
          (if TraceEdgePairCross false true f then 1 else 0) +
            (if TraceEdgePairCross true false f then 1 else 0) +
              (if TraceEdgePairCross true true f then 1 else (0 : ℕ)) := by
  classical
  simp only [traceEdgePair_injective_iff f hf]
  have h01 := hf.1.ne
  have h23 := hf.2.ne
  by_cases h02 : f 0 = f 2 <;> by_cases h03 : f 0 = f 3 <;>
    by_cases h12 : f 1 = f 2 <;> by_cases h13 : f 1 = f 3 <;>
      simp_all [TraceEdgePairCross, TraceEdgePairDiagonal, traceEdgePairReindex]

variable [Fintype V]

noncomputable def traceEdgePairWords (G : SimpleGraph V) : Finset (Fin 4 → V) := by
  classical
  exact Finset.univ.filter (IsTraceEdgePair G)

noncomputable def traceDisjointEdgeWords (G : SimpleGraph V) : Finset (Fin 4 → V) := by
  classical
  exact (traceEdgePairWords G).filter Function.Injective

noncomputable def traceEdgePairCrossWords (G : SimpleGraph V) (left right : Bool) :
    Finset (Fin 4 → V) := by
  classical
  exact (traceEdgePairWords G).filter (TraceEdgePairCross left right)

noncomputable def traceEdgePairDiagonalWords (G : SimpleGraph V) (reverse : Bool) :
    Finset (Fin 4 → V) := by
  classical
  exact (traceEdgePairWords G).filter (TraceEdgePairDiagonal reverse)

noncomputable def traceOrientedEdges (G : SimpleGraph V) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun p => G.Adj p.1 p.2)

theorem mem_traceEdgePairWords_iff (f : Fin 4 → V) :
    f ∈ traceEdgePairWords G ↔ IsTraceEdgePair G f := by
  classical
  simp [traceEdgePairWords]

theorem mem_traceDisjointEdgeWords_iff (f : Fin 4 → V) :
    f ∈ traceDisjointEdgeWords G ↔ IsTraceEdgePair G f ∧ Function.Injective f := by
  classical
  simp [traceDisjointEdgeWords, mem_traceEdgePairWords_iff]

theorem mem_traceEdgePairCrossWords_iff (left right : Bool) (f : Fin 4 → V) :
    f ∈ traceEdgePairCrossWords G left right ↔
      IsTraceEdgePair G f ∧ TraceEdgePairCross left right f := by
  classical
  simp [traceEdgePairCrossWords, mem_traceEdgePairWords_iff]

theorem mem_traceEdgePairDiagonalWords_iff (reverse : Bool) (f : Fin 4 → V) :
    f ∈ traceEdgePairDiagonalWords G reverse ↔
      IsTraceEdgePair G f ∧ TraceEdgePairDiagonal reverse f := by
  classical
  simp [traceEdgePairDiagonalWords, mem_traceEdgePairWords_iff]

theorem mem_traceOrientedEdges_iff (p : V × V) :
    p ∈ traceOrientedEdges G ↔ G.Adj p.1 p.2 := by
  classical
  simp [traceOrientedEdges]

open scoped Classical in
theorem trace_edge_pair_filter_reindex_card (left right : Bool)
    (P : (Fin 4 → V) → Prop) :
    ((traceEdgePairWords G).filter (fun f => P (traceEdgePairReindex left right f))).card =
      ((traceEdgePairWords G).filter P).card := by
  classical
  apply Finset.card_bij (fun f _ => traceEdgePairReindex left right f)
  · intro f hf
    obtain ⟨hp, hP⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨(mem_traceEdgePairWords_iff _).mpr
      (traceEdgePairReindex_isPair left right f ((mem_traceEdgePairWords_iff f).mp hp)), hP⟩
  · intro f _ g _ he
    have hh := congrArg (traceEdgePairReindex left right) he
    simpa only [traceEdgePairReindex_involutive] using hh
  · intro g hg
    obtain ⟨hp, hP⟩ := Finset.mem_filter.mp hg
    refine ⟨traceEdgePairReindex left right g, Finset.mem_filter.mpr ⟨?_, ?_⟩,
      traceEdgePairReindex_involutive left right g⟩
    · exact (mem_traceEdgePairWords_iff _).mpr
        (traceEdgePairReindex_isPair left right g ((mem_traceEdgePairWords_iff g).mp hp))
    · simpa only [traceEdgePairReindex_involutive] using hP

theorem trace_edge_pair_card_balance :
    (traceEdgePairWords G).card + (traceEdgePairDiagonalWords G false).card +
        (traceEdgePairDiagonalWords G true).card =
      (traceDisjointEdgeWords G).card + (traceEdgePairCrossWords G false false).card +
        (traceEdgePairCrossWords G false true).card +
          (traceEdgePairCrossWords G true false).card +
            (traceEdgePairCrossWords G true true).card := by
  classical
  have hs : (∑ f ∈ traceEdgePairWords G,
      (1 + (if TraceEdgePairDiagonal false f then 1 else 0) +
        (if TraceEdgePairDiagonal true f then 1 else 0))) =
      ∑ f ∈ traceEdgePairWords G,
        ((if Function.Injective f then 1 else 0) +
          (if TraceEdgePairCross false false f then 1 else 0) +
            (if TraceEdgePairCross false true f then 1 else 0) +
              (if TraceEdgePairCross true false f then 1 else 0) +
                (if TraceEdgePairCross true true f then 1 else (0 : ℕ))) :=
    Finset.sum_congr rfl (fun f hf => traceEdgePair_indicator_balance f
      ((mem_traceEdgePairWords_iff f).mp hf))
  simp only [Finset.sum_add_distrib, ← Finset.card_eq_sum_ones,
    ← Finset.card_filter] at hs
  exact hs

end TaskH.Six

#print axioms TaskH.Six.traceEdgePairReindex_involutive
#print axioms TaskH.Six.traceEdgePairReindex_isPair
#print axioms TaskH.Six.traceEdgePair_injective_iff
#print axioms TaskH.Six.traceEdgePair_indicator_balance
#print axioms TaskH.Six.mem_traceEdgePairWords_iff
#print axioms TaskH.Six.mem_traceDisjointEdgeWords_iff
#print axioms TaskH.Six.mem_traceEdgePairCrossWords_iff
#print axioms TaskH.Six.mem_traceEdgePairDiagonalWords_iff
#print axioms TaskH.Six.mem_traceOrientedEdges_iff
#print axioms TaskH.Six.trace_edge_pair_filter_reindex_card
#print axioms TaskH.Six.trace_edge_pair_card_balance
