import Research.Backfill.Paper7.MatrixInertiaEmbeddings
import Research.Backfill.Paper7.SpectralThresholdCounts

/-! An exact open-interval budget for induced principal subgraphs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroCutGap
open Matrix BackfillPaper7.Challenge Paper7Comparison

def openGapCount {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : ℝ) : ℕ :=
  ((spec G).filter (fun x => a < x ∧ x < b)).card
#print axioms Paper7IntroCutGap.openGapCount

theorem openGapCount_add_Nge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : ℝ) (hab : a < b) :
    openGapCount G a b + Nge G b = Ngt G a := by
  have hleft : ((spec G).filter (fun x => a < x)).filter (fun x => x < b) =
      (spec G).filter (fun x => a < x ∧ x < b) := by
    rw [Multiset.filter_filter]
    apply Multiset.filter_congr
    intro x _hx
    exact and_comm
  have hright : ((spec G).filter (fun x => a < x)).filter (fun x => ¬x < b) =
      (spec G).filter (fun x => b ≤ x) := by
    rw [Multiset.filter_filter]
    apply Multiset.filter_congr
    intro x _hx
    constructor
    · exact fun h => le_of_not_gt h.1
    · intro h
      exact ⟨not_lt_of_ge h, hab.trans_le h⟩
  have h := congrArg Multiset.card
    (Multiset.filter_add_not (fun x : ℝ => x < b) ((spec G).filter (fun x => a < x)))
  rw [hleft, hright, Multiset.card_add] at h
  exact h
#print axioms Paper7IntroCutGap.openGapCount_add_Nge

theorem induced_adjacency_shift
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (f : W → V)
    (hf : Function.Injective f) (hAdj : ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j))
    (t : ℝ) :
    (G.adjMatrix ℝ - Matrix.scalar V t).submatrix f f =
      H.adjMatrix ℝ - Matrix.scalar W t := by
  have hA : (G.adjMatrix ℝ).submatrix f f = H.adjMatrix ℝ := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply, hAdj]
  have hD : (Matrix.scalar V t).submatrix f f = Matrix.scalar W t := by
    simpa only [Matrix.scalar_apply, Function.comp_def] using
      Matrix.submatrix_diagonal (fun _ : V => t) f hf
  change (G.adjMatrix ℝ).submatrix f f - (Matrix.scalar V t).submatrix f f = _
  rw [hA, hD]
#print axioms Paper7IntroCutGap.induced_adjacency_shift

theorem induced_threshold_budget
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (f : W → V)
    (hf : Function.Injective f) (hAdj : ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j))
    (k : ℕ) (hcard : Fintype.card W + k = Fintype.card V) (t : ℝ) :
    Ngt H t ≤ Ngt G t ∧ Nge G t ≤ Nge H t + k := by
  have hGm : (G.adjMatrix ℝ - Matrix.scalar V t).IsHermitian := by
    exact (Matrix.isHermitian_iff_isSymm.mpr G.isSymm_adjMatrix).sub
      (by simpa only [Matrix.scalar_apply] using Matrix.isHermitian_diagonal (fun _ : V => t))
  have hHm : (H.adjMatrix ℝ - Matrix.scalar W t).IsHermitian := by
    exact (Matrix.isHermitian_iff_isSymm.mpr H.isSymm_adjMatrix).sub
      (by simpa only [Matrix.scalar_apply] using Matrix.isHermitian_diagonal (fun _ : W => t))
  have hp := (principal_inertia_bounds (G.adjMatrix ℝ - Matrix.scalar V t) hGm f hf).1
  have hn := (principal_negative_inertia_bounds
    (G.adjMatrix ℝ - Matrix.scalar V t) hGm f hf).1
  rw [induced_adjacency_shift G H f hf hAdj t] at hp hn
  have htotalG := inertia_total (G.adjMatrix ℝ - Matrix.scalar V t) hGm
  have htotalH := inertia_total (H.adjMatrix ℝ - Matrix.scalar W t) hHm
  have hgeG := nonneg_shift_eq_Nge G t
  have hgeH := nonneg_shift_eq_Nge H t
  constructor
  · simpa only [nPos_shift_eq_Ngt] using hp
  · omega
#print axioms Paper7IntroCutGap.induced_threshold_budget

theorem induced_open_gap_budget
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (f : W → V)
    (hf : Function.Injective f) (hAdj : ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j))
    (k : ℕ) (hcard : Fintype.card W + k = Fintype.card V)
    (a b : ℝ) (hab : a < b) : openGapCount H a b ≤ openGapCount G a b + k := by
  have hg := openGapCount_add_Nge G a b hab
  have hh := openGapCount_add_Nge H a b hab
  have ha := (induced_threshold_budget G H f hf hAdj k hcard a).1
  have hb := (induced_threshold_budget G H f hf hAdj k hcard b).2
  omega
#print axioms Paper7IntroCutGap.induced_open_gap_budget

end Paper7IntroCutGap
