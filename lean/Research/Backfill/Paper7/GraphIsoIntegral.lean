import Research.Backfill.Paper7.SpectrumGraphBasics

/-! Complex characteristic roots and vertex cardinality under actual graph isomorphism. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Normalize
open BackfillPaper7.Challenge

theorem graphIso_charpoly {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) :
    (H.adjMatrix ℂ).charpoly = (G.adjMatrix ℂ).charpoly := by
  rw [← e.reindex_adjMatrix ℂ]
  exact Matrix.charpoly_reindex e.toEquiv (G.adjMatrix ℂ)
#print axioms Paper7Normalize.graphIso_charpoly

theorem graphIso_integral {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H)
    (hG : IsIntegralGraph G) : IsIntegralGraph H := by
  intro x hx
  apply hG x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hx ⊢
  rwa [graphIso_charpoly G H e] at hx
#print axioms Paper7Normalize.graphIso_integral

end Paper7Normalize
