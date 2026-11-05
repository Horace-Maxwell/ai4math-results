import Research.Backfill.Paper7.VersionCanonicalGuards
import Research.Backfill.Paper7.PQListCoverage
import Research.Backfill.Paper7.CertifiedOutputExactness

/-! Genuine partial connections to conjuncts 9 and 11. The all-version forward
implication still needs every Stage guard's independent spectral soundness. -/
set_option autoImplicit false
noncomputable section
namespace Paper7PruningCanonical
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

/-- Complete original ninth-conjunct instance for every no-pruning D3 flag
combination. The domain still allows odd b here. -/
theorem d3_noPruning_leaf (c l w : Bool) (b N : ℕ)
    (hdom : RunDomain (.d3 c l w true) b N) (x : PQ b) (hx : Budget b N x)
    (hG : IsIntegralGraph (SG b x.1 x.2)) : ∃ σ : Fin b → Fin b,
      IsDihedral b σ ∧ reindex σ x ∈ LeafSet (.d3 c l w true) b N := by
  obtain ⟨σ, hσ, hbudget, _hIntegral, hguards⟩ :=
    exists_version_representative (.d3 c l w true) b N hdom.1 hdom.2.2.1 x hx hG
  refine ⟨σ, hσ, ?_, ?_⟩
  · rw [Paper7Pruning.enumerated_eq_budget b N hdom.2.1]
    exact hbudget
  · change Budget b N (reindex σ x) ∧
      (true = false → MomentPass l true false b N (reindex σ x)) ∧
      (c = true → Canonical (if w then keyWeight else key64) w b (reindex σ x)) ∧
      (w = true → RotationRule (fun p q => p+2*q) b (reindex σ x))
    exact And.intro hbudget (And.intro (by intro h; cases h)
      (And.intro hguards.1 hguards.2))
#print axioms Paper7PruningCanonical.d3_noPruning_leaf

/-- The reverse direction of original conjunct 11 holds for every version,
without any assumption that a pruning guard was sound. -/
theorem certified_orbit_integral (v : SearchVersion) (b N : ℕ) (hb : 3 ≤ b)
    (x : PQ b) (hcert : ∃ σ : Fin b → Fin b,
      IsDihedral b σ ∧ reindex σ x ∈ CertifiedOutputs v b N) :
    IsIntegralGraph (SG b x.1 x.2) := by
  obtain ⟨σ, hσ, hout⟩ := hcert
  have hG := (Paper7Pruning.certifiedOutputs_iff v b N (reindex σ x)).mp hout |>.2
  exact (reindex_integral_iff b hb σ hσ x).mp hG
#print axioms Paper7PruningCanonical.certified_orbit_integral

/-- Complete original eleventh-conjunct instance for all no-pruning D3 flags;
no arbitrary graph-isomorphism or extra spectral assumptions occur. -/
theorem d3_noPruning_certified_iff (c l w : Bool) (b N : ℕ)
    (hdom : RunDomain (.d3 c l w true) b N) (x : PQ b) (hx : Budget b N x) :
    IsIntegralGraph (SG b x.1 x.2) ↔ ∃ σ : Fin b → Fin b,
      IsDihedral b σ ∧ reindex σ x ∈ CertifiedOutputs (.d3 c l w true) b N := by
  constructor
  · intro hG
    obtain ⟨σ, hσ, hleaf⟩ := d3_noPruning_leaf c l w b N hdom x hx hG
    refine ⟨σ, hσ, ?_⟩
    exact (Paper7Pruning.certifiedOutputs_iff _ b N _).mpr
      ⟨hleaf, (reindex_integral_iff b hdom.1 σ hσ x).mpr hG⟩
  · exact certified_orbit_integral _ b N hdom.1 x
#print axioms Paper7PruningCanonical.d3_noPruning_certified_iff

end Paper7PruningCanonical
