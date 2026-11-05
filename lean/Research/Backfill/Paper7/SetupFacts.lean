import Research.Backfill.Paper7.SunTheta
import Research.Backfill.Paper7.SunLeafCounts
import Research.Backfill.Paper7.CycleDihedralExact

set_option autoImplicit false

noncomputable section

namespace Paper7Setup

open SimpleGraph BackfillPaper7.Challenge

/-- An actual sun-graph isomorphism recovers both arm counts at its induced
root permutation: p is the degree-one neighbor count, and q follows from degree. -/
theorem sg_iso_root_parameters (b : ℕ) (p q p' q' : Fin b → ℕ) (hb : 3 ≤ b)
    (e : SG b p q ≃g SG b p' q') (k : Fin b) :
    p' (sunIsoRootMap hb e k) = p k ∧ q' (sunIsoRootMap hb e k) = q k := by
  have hcards := leaf_neighbor_card_iso (SG b p q) (SG b p' q') e (Sum.inl k)
  rw [sunIsoRootMap_spec hb e k,
    sg_leaf_neighbor_card b p q hb k,
    sg_leaf_neighbor_card b p' q' hb (sunIsoRootMap hb e k)] at hcards
  have hdegrees := e.degree_eq (Sum.inl k)
  rw [sunIsoRootMap_spec hb e k,
    sg_root_degree b p q hb k,
    sg_root_degree b p' q' hb (sunIsoRootMap hb e k)] at hdegrees
  exact ⟨hcards.symm, by omega⟩

#print axioms Paper7Setup.sg_iso_root_parameters

theorem sg_isomorphism_iff_dihedral (b : ℕ) (p q p' q' : Fin b → ℕ) (hb : 3 ≤ b) :
    Nonempty (SG b p q ≃g SG b p' q') ↔
      ∃ σ : Fin b → Fin b, IsDihedral b σ ∧ p' = p ∘ σ ∧ q' = q ∘ σ := by
  constructor
  · rintro ⟨e⟩
    let σ := sunIsoRootIso hb e.symm
    refine ⟨σ, cycle_iso_isDihedral b hb σ, ?_, ?_⟩
    · funext k
      exact (sg_iso_root_parameters b p' q' p q hb e.symm k).1.symm
    · funext k
      exact (sg_iso_root_parameters b p' q' p q hb e.symm k).2.symm
  · rintro ⟨σ, hσ, hp, hq⟩
    exact sg_iso_of_dihedral b p q p' q' hb σ hσ hp hq

#print axioms Paper7Setup.sg_isomorphism_iff_dihedral

theorem check_SetupFacts : BackfillPaper7.Challenge.SetupFacts := by
  intro b p q hb
  refine ⟨sg_order b p q, sg_edges b p q hb, sg_theta b p q hb, ?_⟩
  intro p' q'
  exact sg_isomorphism_iff_dihedral b p q p' q' hb

#print axioms Paper7Setup.check_SetupFacts

end Paper7Setup
