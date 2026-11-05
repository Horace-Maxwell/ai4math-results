import Research.Backfill.Paper7.SchwenkRowMinors
import Research.Backfill.Paper7.GraphPhiCharpoly

/-! The exact edge identity for any finite simple graph, with the remaining
single-path contribution still explicitly an adjugate entry. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicSchwenk
open Polynomial SimpleGraph BackfillPaper7.Challenge.Legacy.Algebra
open scoped Classical

theorem graph_charmatrix_entry {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
    Matrix.charmatrix (G.adjMatrix ℤ) i j =
      if i = j then X else if G.Adj i j then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [Matrix.charmatrix_apply_eq]
  · rw [Matrix.charmatrix_apply_ne _ _ _ hij]
    by_cases ha : G.Adj i j <;> simp [hij, ha, SimpleGraph.adjMatrix_apply]
#print axioms Paper7UnicyclicSchwenk.graph_charmatrix_entry

theorem graph_charmatrix_isSymm {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Matrix.charmatrix (G.adjMatrix ℤ)).IsSymm := by
  change (Matrix.diagonal (fun _ : V => (X : Polynomial ℤ)) -
    (G.adjMatrix ℤ).map C).IsSymm
  exact (Matrix.isSymm_diagonal _).sub (G.isSymm_adjMatrix.map C)
#print axioms Paper7UnicyclicSchwenk.graph_charmatrix_isSymm

/-- A genuine induced deletion is the principal submatrix, for every deletion
set, including the empty set and the whole vertex set. -/
theorem graph_charmatrix_deleteVertices {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) :
    (Matrix.charmatrix (G.adjMatrix ℤ)).submatrix
      (fun x : {x : V // x ∉ S} => x.val) (fun x : {x : V // x ∉ S} => x.val) =
      Matrix.charmatrix ((deleteVertices G S).adjMatrix ℤ) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix, Matrix.of_apply, deleteVertices,
    SimpleGraph.induce_adj, Subtype.ext_iff]

#print axioms Paper7UnicyclicSchwenk.graph_charmatrix_deleteVertices

/-- Removing an edge touching a deleted vertex does not change the remaining
induced graph. Only membership of one endpoint is needed. -/
theorem deleteVertices_deleteEdge {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (S : Set V) (hu : u ∈ S) :
    deleteVertices (G.deleteEdges ({s(u,v)} : Set (Sym2 V))) S =
      deleteVertices G S := by
  ext i j
  change (G.deleteEdges ({s(u,v)} : Set (Sym2 V))).Adj i.val j.val ↔ G.Adj i.val j.val
  have hne : s(i.val,j.val) ≠ s(u,v) := by
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact i.property (h.1.symm ▸ hu)
    · exact j.property (h.2.symm ▸ hu)
  simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, hne, not_false_eq_true,
    and_true]
#print axioms Paper7UnicyclicSchwenk.deleteVertices_deleteEdge

theorem edge_charmatrix_rows {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (huv : G.Adj u v) :
    let D := Matrix.charmatrix ((G.deleteEdges ({s(u,v)} : Set (Sym2 V))).adjMatrix ℤ)
    Matrix.charmatrix (G.adjMatrix ℤ) =
      (D.updateRow u (D u + Pi.single v (-1))).updateRow v (D v + Pi.single u (-1)) := by
  dsimp only
  apply Matrix.ext
  intro i j
  have hne : u ≠ v := huv.ne
  have hvu : G.Adj v u := (G.adj_comm v u).mpr huv
  by_cases hiu : i = u
  · subst i
    by_cases hju : j = u
    · subst j
      simp [Matrix.updateRow_apply, hne]
    · by_cases hjv : j = v
      · subst j
        simp [Matrix.updateRow_apply, huv, hne,
          SimpleGraph.deleteEdges_adj]
      · simp [Matrix.updateRow_apply, hne, hju, hjv,
          Ne.symm hju, SimpleGraph.deleteEdges_adj]
  · by_cases hiv : i = v
    · subst i
      by_cases hju : j = u
      · subst j
        simp [Matrix.updateRow_apply, hvu, Ne.symm hne,
          SimpleGraph.deleteEdges_adj, Sym2.eq_swap]
      · by_cases hjv : j = v
        · subst j
          simp [Matrix.updateRow_apply, Ne.symm hne]
        · simp [Matrix.updateRow_apply, hju, hjv,
            Ne.symm hjv, SimpleGraph.deleteEdges_adj]
    · simp [Matrix.updateRow_apply, graph_charmatrix_entry, hiu, hiv,
        SimpleGraph.deleteEdges_adj]
#print axioms Paper7UnicyclicSchwenk.edge_charmatrix_rows

/-- Exact universal edge formula. The last term is an actual adjugate entry,
not an assumed path-deletion or cycle-deletion polynomial. -/
theorem graphPhi_edge_adjugate {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (huv : G.Adj u v) :
    let T := G.deleteEdges ({s(u,v)} : Set (Sym2 V))
    graphPhi G = graphPhi T - graphPhi (deleteVertices G ({u,v} : Set V)) -
      2 * (Matrix.charmatrix (T.adjMatrix ℤ)).adjugate v u := by
  dsimp only
  let T := G.deleteEdges ({s(u,v)} : Set (Sym2 V))
  let D := Matrix.charmatrix (T.adjMatrix ℤ)
  have hrest : (D.submatrix
      (fun x : {x : V // x ∉ ({u,v} : Set V)} => x.val)
      (fun x : {x : V // x ∉ ({u,v} : Set V)} => x.val)).det =
      graphPhi (deleteVertices G ({u,v} : Set V)) := by
    rw [graph_charmatrix_deleteVertices T]
    rw [deleteVertices_deleteEdge G u v ({u,v} : Set V) (by simp)]
    exact (Paper7GraphPhi.graphPhi_eq_charpoly _).symm
  calc
    graphPhi G = (Matrix.charmatrix (G.adjMatrix ℤ)).det :=
      Paper7GraphPhi.graphPhi_eq_charpoly G
    _ = ((D.updateRow u (D u + Pi.single v (-1))).updateRow v
        (D v + Pi.single u (-1))).det :=
      congrArg Matrix.det (edge_charmatrix_rows G u v huv)
    _ = D.det - (D.submatrix
        (fun x : {x : V // x ∉ ({u,v} : Set V)} => x.val)
        (fun x : {x : V // x ∉ ({u,v} : Set V)} => x.val)).det -
        2 * D.adjugate v u :=
      symmetric_edge_row_expansion D (graph_charmatrix_isSymm T) u v huv.ne
    _ = graphPhi T - graphPhi (deleteVertices G ({u,v} : Set V)) -
        2 * D.adjugate v u :=
      congrArg₂ (fun x y : Polynomial ℤ => x - y - 2 * D.adjugate v u)
        (Paper7GraphPhi.graphPhi_eq_charpoly T).symm hrest
#print axioms Paper7UnicyclicSchwenk.graphPhi_edge_adjugate

theorem graph_adjugate_diagonal {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    (Matrix.charmatrix (G.adjMatrix ℤ)).adjugate u u =
      graphPhi (deleteVertices G ({u} : Set V)) := by
  rw [adjugate_diagonal_eq_complement, graph_charmatrix_deleteVertices]
  exact (Paper7GraphPhi.graphPhi_eq_charpoly _).symm
#print axioms Paper7UnicyclicSchwenk.graph_adjugate_diagonal

/-- Empty vertex complements contribute exactly one. -/
theorem graphPhi_isEmpty {V : Type} [Fintype V] [DecidableEq V] [IsEmpty V]
    (G : SimpleGraph V) : graphPhi G = 1 := by
  unfold graphPhi Matrix.charpoly
  exact Matrix.det_isEmpty
#print axioms Paper7UnicyclicSchwenk.graphPhi_isEmpty

end Paper7UnicyclicSchwenk
