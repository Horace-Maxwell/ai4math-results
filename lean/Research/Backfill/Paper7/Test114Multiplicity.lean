import Research.Backfill.Paper7.Test114Eigenspace
import Research.Backfill.Paper7.Test114SpectralMultiplicity

/-! Algebraic multiplicity is obtained from Mathlib's real symmetric spectral
theorem, then specialized to the exact unchanged test_114_required. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open scoped Matrix
noncomputable section
namespace Paper7Test114
open BackfillPaper7.Challenge

theorem adjacency_hermitian : A.IsHermitian := by
  exact Matrix.isHermitian_iff_isSymm.mpr (G.isSymm_adjMatrix (α := ℝ))
#print axioms Paper7Test114.adjacency_hermitian

/-- Count the eigenvalue list; this preserves multiplicity, not merely membership. -/
theorem count_roots_eq_finrank : A.charpoly.roots.count (1 : ℝ) = Module.finrank ℝ E := by
  exact Paper7Test114Generic.realHermitian_count_roots A adjacency_hermitian (1 : ℝ)
#print axioms Paper7Test114.count_roots_eq_finrank

theorem multiplicity_one : mult G 1 = 19 := by
  change A.charpoly.roots.count (1 : ℝ) = 19
  exact count_roots_eq_finrank.trans eigenspace_finrank
#print axioms Paper7Test114.multiplicity_one

end Paper7Test114

namespace Paper7StatementTestsV3

theorem test114 : BackfillPaper7.Challenge.LegacyTests.test_114_required := by
  change BackfillPaper7.Challenge.mult Paper7Test114.G 1 = 19 ∧
    ¬ BackfillPaper7.Challenge.mult Paper7Test114.G 1 ≤ 4
  constructor
  · exact Paper7Test114.multiplicity_one
  · rw [Paper7Test114.multiplicity_one]
    omega
#print axioms Paper7StatementTestsV3.test114

end Paper7StatementTestsV3
