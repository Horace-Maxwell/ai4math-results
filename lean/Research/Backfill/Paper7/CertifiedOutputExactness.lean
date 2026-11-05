import Research.Backfill.Paper7.LegacyEnumeration
import Research.Backfill.Paper7.SpectrumFactorization
import Research.Backfill.Paper7.GraphPhiCharpoly

/-! Source-only candidate. The certificate is equivalent to genuine integral
spectrum; neither modular survival nor search completeness is assumed. -/
set_option autoImplicit false
noncomputable section

namespace Paper7Pruning
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open BackfillPaper7.Challenge.Legacy.Algebra

theorem graph_factor_list_iff_integral {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ roots : List ℤ, (G.adjMatrix ℤ).charpoly =
      (roots.map (fun z => (X - C z : Polynomial ℤ))).prod) ↔ IsIntegralGraph G := by
  classical
  constructor
  · rintro ⟨roots, hroots⟩
    apply (Paper7Spectrum.integral_iff_integerFactorization G).mpr
    refine ⟨roots.toFinset, roots, ?_, ?_⟩
    · intro z hz
      exact List.mem_toFinset.mpr hz
    · exact (Paper7GraphPhi.graphPhi_eq_charpoly G).trans hroots
  · intro hG
    obtain ⟨_S, roots, _hS, hroots⟩ :=
      (Paper7Spectrum.integral_iff_integerFactorization G).mp hG
    exact ⟨roots, (Paper7GraphPhi.graphPhi_eq_charpoly G).symm.trans hroots⟩
#print axioms Paper7Pruning.graph_factor_list_iff_integral

theorem integerFactorCertificate_iff (b : ℕ) (x : PQ b) :
    IntegerFactorCertificate b x ↔ IsIntegralGraph (SG b x.1 x.2) :=
  graph_factor_list_iff_integral (SG b x.1 x.2)
#print axioms Paper7Pruning.integerFactorCertificate_iff

theorem certifiedOutputs_iff (v : SearchVersion) (b N : ℕ) (x : PQ b) :
    x ∈ CertifiedOutputs v b N ↔
      x ∈ LeafSet v b N ∧ IsIntegralGraph (SG b x.1 x.2) := by
  change (_ ∧ IntegerFactorCertificate b x) ↔ _
  rw [integerFactorCertificate_iff]
#print axioms Paper7Pruning.certifiedOutputs_iff

end Paper7Pruning
