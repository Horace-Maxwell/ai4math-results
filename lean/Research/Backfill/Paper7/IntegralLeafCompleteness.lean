import Research.Backfill.Paper7.IntegralStageGuards
import Research.Backfill.Paper7.CanonicalLeafConnections

/-! Source-only all-version completeness. First select an actual isomorphic
budget representative, then prove every prefix guard on that new graph. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningGuards
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7PruningCanonical

theorem integral_has_leaf (v : SearchVersion) (b N : ℕ) (hdom : RunDomain v b N)
    (x : PQ b) (hx : Budget b N x) (hG : IsIntegralGraph (SG b x.1 x.2)) :
    ∃ σ : Fin b → Fin b, IsDihedral b σ ∧ reindex σ x ∈ LeafSet v b N := by
  obtain ⟨σ, hσ, hbudget, hIntegral, hguards⟩ :=
    exists_version_representative v b N hdom.1 hdom.2.2.1 x hx hG
  refine ⟨σ, hσ, ?_, ?_⟩
  · rw [Paper7Pruning.enumerated_eq_budget b N hdom.2.1]
    exact hbudget
  · exact stage_integral_of_guards v b N hdom.1 hdom.2.2.1
      (reindex σ x) hbudget hIntegral hguards
#print axioms Paper7PruningGuards.integral_has_leaf

theorem integral_iff_certified_orbit (v : SearchVersion) (b N : ℕ)
    (hdom : RunDomain v b N) (x : PQ b) (hx : Budget b N x) :
    IsIntegralGraph (SG b x.1 x.2) ↔
      ∃ σ : Fin b → Fin b, IsDihedral b σ ∧ reindex σ x ∈ CertifiedOutputs v b N := by
  constructor
  · intro hG
    obtain ⟨σ, hσ, hleaf⟩ := integral_has_leaf v b N hdom x hx hG
    refine ⟨σ, hσ, ?_⟩
    exact (Paper7Pruning.certifiedOutputs_iff v b N (reindex σ x)).mpr
      ⟨hleaf, (reindex_integral_iff b hdom.1 σ hσ x).mpr hG⟩
  · exact certified_orbit_integral v b N hdom.1 x
#print axioms Paper7PruningGuards.integral_iff_certified_orbit

end Paper7PruningGuards
