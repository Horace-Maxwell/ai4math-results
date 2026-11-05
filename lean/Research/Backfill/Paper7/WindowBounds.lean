import Research.Backfill.Paper7.TraceWalkCounts
import Research.Backfill.Paper7.SetupCardinality

set_option autoImplicit false

noncomputable section

namespace Paper7SpectralWindow

open BackfillPaper7.Challenge

/-- Each real adjacency eigenvalue contributes a nonnegative term to the
second spectral moment, so its square is bounded by twice the edge count. -/
theorem spec_square_le_twice_edges {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : ℝ) (hx : x ∈ spec G) : x ^ 2 ≤ 2 * (G.edgeFinset.card : ℝ) := by
  have hnonneg : ∀ z ∈ (spec G).map (fun y => y ^ 2), (0 : ℝ) ≤ z := by
    intro z hz
    obtain ⟨y, _hy, rfl⟩ := Multiset.mem_map.mp hz
    exact sq_nonneg y
  calc
    x ^ 2 ≤ ((spec G).map (fun y => y ^ 2)).sum :=
      Multiset.single_le_sum hnonneg (x ^ 2) (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
    _ = 2 * (G.edgeFinset.card : ℝ) := Paper7Moments.graph_second_moment G

#print axioms Paper7SpectralWindow.spec_square_le_twice_edges

/-- The complete analytic part of the frozen window contract. Integrality
is not needed for either bound. -/
theorem sun_spectral_window (b : ℕ) (p q : Fin b → ℕ)
    (hb : 3 ≤ b) (hn : nOf b p q ≤ 49)
    (x : ℝ) (hx : x ∈ spec (SG b p q)) :
    x ^ 2 ≤ 2 * (nOf b p q : ℝ) ∧ |x| < 10 := by
  have hsq : x ^ 2 ≤ 2 * (nOf b p q : ℝ) := by
    simpa only [Paper7Setup.sg_edges b p q hb] using
      spec_square_le_twice_edges (SG b p q) x hx
  have hnR : (nOf b p q : ℝ) ≤ 49 := by exact_mod_cast hn
  refine ⟨hsq, ?_⟩
  apply abs_lt_of_sq_lt_sq (b := (10 : ℝ))
  · nlinarith
  · norm_num

#print axioms Paper7SpectralWindow.sun_spectral_window

end Paper7SpectralWindow
