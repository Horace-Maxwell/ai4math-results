import Research.Backfill.Paper7.MatrixInertiaEmbeddings
import Research.Backfill.Paper7.SpectralThresholdCounts
import Research.Backfill.Paper7.SunGraphAdjacency

/-! Actual induced-cycle comparison at every real threshold. This does not
assert the unproved explicit cycle eigenvalue-count formula. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace Paper7Lemma41
open BackfillPaper7.Challenge Paper7Comparison Paper7Cleared

theorem shiftedGraph_isHermitian {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : ℝ) :
    (G.adjMatrix ℝ - Matrix.scalar V x).IsHermitian := by
  rw [Matrix.scalar_apply]
  exact (G.isHermitian_adjMatrix ℝ).sub (Matrix.isHermitian_diagonal _)
#print axioms Paper7Lemma41.shiftedGraph_isHermitian

theorem cycle_shift_principal (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) (x : ℝ) :
    ((sunGraph b L).adjMatrix ℝ - Matrix.scalar (SunV b L) x).submatrix
      (Sum.inl : Fin b → SunV b L) Sum.inl =
        (SimpleGraph.cycleGraph b).adjMatrix ℝ - Matrix.scalar (Fin b) x := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Sum.inl.injEq, SimpleGraph.adjMatrix_apply,
    sun_cycle_adj_iff b L hb]
#print axioms Paper7Lemma41.cycle_shift_principal

/-- Both strict and non-strict interlacing counts on the actual original graph. -/
theorem cycle_interlacing_all_thresholds (b : ℕ) (L : Fin b → List ℕ)
    (hb : 3 ≤ b) (x : ℝ) :
    Ngt (SimpleGraph.cycleGraph b) x ≤ Ngt (sunGraph b L) x ∧
    Nge (SimpleGraph.cycleGraph b) x ≤ Nge (sunGraph b L) x ∧
    Nlt (SimpleGraph.cycleGraph b) x ≤ Nlt (sunGraph b L) x ∧
    Nle (SimpleGraph.cycleGraph b) x ≤ Nle (sunGraph b L) x := by
  let M := (sunGraph b L).adjMatrix ℝ - Matrix.scalar (SunV b L) x
  have hM : M.IsHermitian := shiftedGraph_isHermitian _ _
  have hp := principal_inertia_bounds M hM (Sum.inl : Fin b → SunV b L) Sum.inl_injective
  have hn := principal_negative_inertia_bounds M hM (Sum.inl : Fin b → SunV b L)
    Sum.inl_injective
  dsimp only [M] at hp hn
  rw [cycle_shift_principal b L hb x] at hp hn
  exact ⟨by simpa only [M, nPos_shift_eq_Ngt] using hp.1,
    by simpa only [M, nonneg_shift_eq_Nge] using hp.2,
    by simpa only [M, nNeg_shift_eq_Nlt] using hn.1,
    by simpa only [M, nonpos_shift_eq_Nle] using hn.2⟩
#print axioms Paper7Lemma41.cycle_interlacing_all_thresholds

/-- Exactly the two unconditional comparison clauses of frozen Lemma41. -/
theorem lemma41_interlacing (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    Ngt (SimpleGraph.cycleGraph b) 1 ≤ Ngt (SG b p q) 1 ∧
    Nlt (SimpleGraph.cycleGraph b) (-1) ≤ Nlt (SG b p q) (-1) :=
  ⟨(cycle_interlacing_all_thresholds b (pq b p q) hb 1).1,
    (cycle_interlacing_all_thresholds b (pq b p q) hb (-1)).2.2.1⟩
#print axioms Paper7Lemma41.lemma41_interlacing

end Paper7Lemma41
