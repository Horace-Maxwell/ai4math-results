import Research.Backfill.Paper7.SchwenkPunctureMatrix
import Research.Backfill.Paper7.SchwenkGraphExpansion

/-! The recurrence and the zero term are proved for arbitrary actual finite
graphs. Acyclicity enters only later, in selecting the unique next path vertex. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicSchwenk
open Polynomial SimpleGraph BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Classical

/-- Exact cofactor recurrence in the graph with one vertex removed. The
nonzero determinant needed by the fraction-field calculation is proved here. -/
theorem graph_adjugate_puncture {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (v : {x : V // x ≠ u}) :
    (Matrix.charmatrix (G.adjMatrix ℤ)).adjugate v.val u =
      ∑ z : {x : V // x ≠ u}, if G.Adj z.val u then
        (Matrix.charmatrix ((G.induce {x | x ≠ u}).adjMatrix ℤ)).adjugate v z else 0 := by
  let M := Matrix.charmatrix (G.adjMatrix ℤ)
  have hD : M.submatrix (fun x : {x : V // x ≠ u} => x.val)
      (fun x : {x : V // x ≠ u} => x.val) = Matrix.charmatrix ((G.induce {x | x ≠ u}).adjMatrix ℤ) := by
    apply Matrix.ext
    intro i j
    simp only [M, Matrix.submatrix_apply, graph_charmatrix_entry,
      Subtype.ext_iff, SimpleGraph.induce_adj]
  have hdet : (M.submatrix (fun x : {x : V // x ≠ u} => x.val)
      (fun x : {x : V // x ≠ u} => x.val)).det ≠ 0 := by
    rw [hD]
    exact ((G.induce {x | x ≠ u}).adjMatrix ℤ).charpoly_monic.ne_zero
  rw [polynomial_adjugate_puncture M u v hdet, hD, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro z _
  change -((Matrix.charmatrix ((G.induce {x | x ≠ u}).adjMatrix ℤ)).adjugate v z *
    Matrix.charmatrix (G.adjMatrix ℤ) z.val u) = _
  rw [graph_charmatrix_entry]
  by_cases ha : G.Adj z.val u <;> simp [z.property, ha]
#print axioms Paper7UnicyclicSchwenk.graph_adjugate_puncture

/-- Vertices in different connected components have zero off-diagonal
adjugate entry, without assuming the graph connected or acyclic. -/
theorem graph_adjugate_zero_of_not_reachable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (huv : ¬G.Reachable u v) :
    (Matrix.charmatrix (G.adjMatrix ℤ)).adjugate v u = 0 := by
  apply adjugate_zero_of_closed_block _ {x | G.Reachable u x} u v
    (SimpleGraph.Reachable.refl u) huv
  intro i hi j hj
  have hij : i ≠ j := by
    intro h
    exact hi (h.symm ▸ hj)
  have ha : ¬G.Adj i j := fun h => hi (hj.trans h.symm.reachable)
  simp only [graph_charmatrix_entry, hij, ha, ite_false]
#print axioms Paper7UnicyclicSchwenk.graph_adjugate_zero_of_not_reachable

/-- The characteristic polynomial is unchanged by a genuine vertex
bijection preserving the actual adjacency relation. -/
theorem graphPhi_equiv {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : V ≃ W)
    (he : ∀ i j, H.Adj (e i) (e j) ↔ G.Adj i j) : graphPhi G = graphPhi H := by
  have hm : Matrix.charmatrix (G.adjMatrix ℤ) =
      (Matrix.charmatrix (H.adjMatrix ℤ)).submatrix e e := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, graph_charmatrix_entry, e.injective.eq_iff, he]
  calc
    graphPhi G = (Matrix.charmatrix (G.adjMatrix ℤ)).det :=
      Paper7GraphPhi.graphPhi_eq_charpoly G
    _ = ((Matrix.charmatrix (H.adjMatrix ℤ)).submatrix e e).det := congrArg Matrix.det hm
    _ = (Matrix.charmatrix (H.adjMatrix ℤ)).det := Matrix.det_submatrix_equiv_self e _
    _ = graphPhi H := (Paper7GraphPhi.graphPhi_eq_charpoly H).symm
#print axioms Paper7UnicyclicSchwenk.graphPhi_equiv

end Paper7UnicyclicSchwenk
