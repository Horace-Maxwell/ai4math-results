import Research.Backfill.Paper4.Challenge

/-! A semantic bridge from actual independent vertex sets to a computable finite count.
This auxiliary statement does not establish any frozen classification or numerical target.
Compilation and acceptance are recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4.TriangleFreeIndependentCount

def independentFinsets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.filter (fun s => s.Nonempty ∧ G.IsIndepSet (s : Set V))

theorem actual_set_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nat.card {s : Set V // s.Nonempty ∧ G.IsIndepSet s} =
      (independentFinsets G).card := by
  classical
  let e : {s : Finset V // s.Nonempty ∧ G.IsIndepSet (s : Set V)} ≃
      {s : Set V // s.Nonempty ∧ G.IsIndepSet s} :=
    Fintype.finsetEquivSet.subtypeEquiv (fun s => by
      simp only [Fintype.finsetEquivSet_apply, Finset.coe_nonempty])
  calc
    Nat.card {s : Set V // s.Nonempty ∧ G.IsIndepSet s} =
        Nat.card {s : Finset V // s.Nonempty ∧ G.IsIndepSet (s : Set V)} :=
      Nat.card_congr e.symm
    _ = (independentFinsets G).card :=
      Nat.subtype_card (independentFinsets G) (by
        intro s
        simp only [independentFinsets, Finset.mem_filter, Finset.mem_univ, true_and])

#print axioms actual_set_count

end CodexPaper4.TriangleFreeIndependentCount
