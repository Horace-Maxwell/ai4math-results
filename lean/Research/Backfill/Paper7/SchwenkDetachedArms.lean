import Research.Backfill.Paper7.SchwenkDeletionBasics
import Research.Backfill.Paper7.SunGraphBlocks
import Research.Backfill.Paper7.SunPendantAssembly

/-! Deletion is the original induced graph on the complement of all cycle
vertices. Every arm vertex, including every detached endpoint arm, is retained. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Schwenk
open Polynomial Finset BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Cleared
open scoped Classical

def cycleComplementEquiv (b : ℕ) (L : Fin b → List ℕ) :
    {v : SunV b L // v ∉ sunCycleVertices b L} ≃ ArmV b L where
  toFun := fun x => by
    rcases x with ⟨x, hx⟩
    cases x with
    | inl k => exact False.elim (hx ⟨k, rfl⟩)
    | inr a => exact a
  invFun := fun a => ⟨Sum.inr a, by rintro ⟨k, hk⟩; cases hk⟩
  left_inv := by
    rintro ⟨x, hx⟩
    cases x with
    | inl k => exact False.elim (hx ⟨k, rfl⟩)
    | inr a => rfl
  right_inv := fun _ => rfl
#print axioms Paper7Schwenk.cycleComplementEquiv

theorem delete_cycle_charmatrix (b : ℕ) (L : Fin b → List ℕ) :
    (Matrix.charmatrix
      ((deleteVertices (sunGraph b L) (sunCycleVertices b L)).adjMatrix ℤ)).reindex
        (cycleComplementEquiv b L) (cycleComplementEquiv b L) =
      pendantShift b L (X : Polynomial ℤ) := by
  rw [graph_charmatrix]
  apply Matrix.ext
  rintro ⟨k, j, a⟩ ⟨k', j', a'⟩
  have h := sun_leaf_shift_entry (K := Polynomial ℤ) b L X k k' j j' a a'
  change
    ((X : Polynomial ℤ) •
      (1 : Matrix {v : SunV b L // v ∉ sunCycleVertices b L}
        {v : SunV b L // v ∉ sunCycleVertices b L} (Polynomial ℤ)) -
      (deleteVertices (sunGraph b L) (sunCycleVertices b L)).adjMatrix (Polynomial ℤ))
        ⟨Sum.inr ⟨k, j, a⟩, _⟩ ⟨Sum.inr ⟨k', j', a'⟩, _⟩ = _
  simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    deleteVertices, SimpleGraph.adjMatrix, Matrix.of_apply, SimpleGraph.induce_adj,
    Subtype.mk.injEq] using h
#print axioms Paper7Schwenk.delete_cycle_charmatrix

/-- Arbitrary arm lists, arbitrary b, and empty fibers are included. -/
theorem graphPhi_delete_cycle (b : ℕ) (L : Fin b → List ℕ) :
    graphPhi (deleteVertices (sunGraph b L) (sunCycleVertices b L)) =
      ∏ k : Fin b, ∏ j : Fin (L k).length,
        (pathShift (X : Polynomial ℤ) ((L k).get j)).det := by
  rw [Paper7GraphPhi.graphPhi_eq_charpoly]
  unfold Matrix.charpoly
  rw [← Matrix.det_reindex_self (cycleComplementEquiv b L), delete_cycle_charmatrix]
  unfold pendantShift
  rw [det_blockDiagonal']
  simp_rw [det_blockDiagonal']
#print axioms Paper7Schwenk.graphPhi_delete_cycle

/-- Exactly the third equality of frozen SchwenkRecurrenceExactness, proved
for every b (hence including all required b>=3) with the original graphPhi. -/
theorem schwenk_cycle_deletion_pq (b : ℕ) (p q : Fin b → ℕ) :
    graphPhi (deleteVertices (SG b p q) (sunCycleVertices b (pq b p q))) =
      ∏ k, legPolynomial (p k) (q k) := by
  change graphPhi (deleteVertices (sunGraph b (pq b p q))
    (sunCycleVertices b (pq b p q))) = _
  rw [graphPhi_delete_cycle]
  apply Finset.prod_congr rfl
  intro k _hk
  exact path_determinants_product b p q (X : Polynomial ℤ) k
#print axioms Paper7Schwenk.schwenk_cycle_deletion_pq

end Paper7Schwenk
