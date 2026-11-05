import Research.Backfill.Paper7.GraphPhiCharpoly

set_option autoImplicit false
noncomputable section
namespace Paper7Schwenk
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped Classical

/-- The empty graph contributes 1, including an empty subtype after deletion. -/
theorem graphPhi_isEmpty {V : Type} [Fintype V] [DecidableEq V] [IsEmpty V]
    (G : SimpleGraph V) : graphPhi G = 1 := by
  unfold graphPhi Matrix.charpoly
  exact Matrix.det_isEmpty
#print axioms Paper7Schwenk.graphPhi_isEmpty

theorem graphPhi_edgeless {V : Type} [Fintype V] [DecidableEq V] :
    graphPhi (⊥ : SimpleGraph V) = X ^ Fintype.card V := by
  rw [Paper7GraphPhi.graphPhi_eq_charpoly]
  have h : (⊥ : SimpleGraph V).adjMatrix ℤ = 0 := by
    ext i j
    simp [SimpleGraph.adjMatrix_apply]
  rw [h, Matrix.charpoly_zero]
#print axioms Paper7Schwenk.graphPhi_edgeless

theorem graphPhi_delete_all {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : graphPhi (deleteVertices G Set.univ) = 1 := by
  let : IsEmpty {v : V // v ∉ (Set.univ : Set V)} :=
    ⟨fun v => v.property (Set.mem_univ v.val)⟩
  exact graphPhi_isEmpty _
#print axioms Paper7Schwenk.graphPhi_delete_all

theorem graph_charmatrix {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix.charmatrix (G.adjMatrix ℤ) =
      (X : Polynomial ℤ) • (1 : Matrix V V (Polynomial ℤ)) -
        G.adjMatrix (Polynomial ℤ) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j <;> by_cases ha : G.Adj i j <;>
    simp [Matrix.sub_apply,
      Matrix.smul_apply, SimpleGraph.adjMatrix_apply, hij, ha]
#print axioms Paper7Schwenk.graph_charmatrix

end Paper7Schwenk
