import Research.Backfill.Paper7.SpectralMoments

/-! The second trace and the exact length-count bridge for arbitrary finite
simple graphs. The fourth-trace and cycle-fibre counts remain separate work. -/

set_option autoImplicit false

noncomputable section

open Finset
open BackfillPaper7.Challenge

namespace Paper7Moments

theorem trace_square {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    ((H.adjMatrix ℤ) ^ 2).trace = 2 * (H.edgeFinset.card : ℤ) := by
  calc
    ((H.adjMatrix ℤ) ^ 2).trace = ∑ v : V, (H.degree v : ℤ) := by
      simp only [pow_two, Matrix.trace, Matrix.diag,
        SimpleGraph.adjMatrix_mul_self_apply_self]
    _ = 2 * (H.edgeFinset.card : ℤ) := by
      exact_mod_cast H.sum_degrees_eq_twice_card_edges

theorem trace_eq_closed_walk_count {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ) :
    ((H.adjMatrix ℤ) ^ k).trace =
      ∑ v : V, (Fintype.card {w : H.Walk v v // w.length = k} : ℤ) := by
  simp only [Matrix.trace, Matrix.diag, SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
  apply Finset.sum_congr rfl
  intro v _
  exact congrArg (fun n : ℕ => (n : ℤ)) (Fintype.card_congr (Equiv.refl _))

theorem graph_second_moment {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    ((spec H).map (fun x => x ^ 2)).sum = 2 * (H.edgeFinset.card : ℝ) := by
  rw [graph_moment_eq_int_trace, trace_square]
  norm_cast

end Paper7Moments

#print axioms Paper7Moments.trace_square
#print axioms Paper7Moments.trace_eq_closed_walk_count
#print axioms Paper7Moments.graph_second_moment
