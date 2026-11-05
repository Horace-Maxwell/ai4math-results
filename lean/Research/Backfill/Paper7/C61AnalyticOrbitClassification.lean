import Research.Backfill.Paper7.C61FourCompleteClassification
import Research.Backfill.Paper7.C61ThreeCompleteExclusion
import Research.Backfill.Paper7.C61PerronFiveCompleteExclusion
import Research.Backfill.Paper7.C61OrbitTransport

/-! NEW SOURCE ONLY. Candidate assembly of the exact frozen C61OrbitSix
contract from the complete original-parameter Perron branches. This file
has no execution receipt and confers no formal acceptance credit. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Analytic
open BackfillPaper7.Challenge
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Higher
open scoped BigOperators Classical

theorem integral_parameters_are_c61 (p q : Fin 6 → ℕ)
    (hp : 0<∑ k, (p k+q k)) (hn : nOf 6 p q≤42)
    (hG : IsIntegralGraph (SG 6 p q)) : q=(fun _ => 0) ∧ p∈C61Rotations := by
  have hs := actual_shapes p q hp hn hG
  rcases hs with h3 | h4 | ⟨h5,h6,_⟩ | ⟨h6,_,_,_,_⟩
  · exact (Paper7C61Three.root_three_impossible p q hn hG h3).elim
  · exact Paper7C61Four.root_four_classification p q hp hn hG h4
  · exact (Paper7C61FiveThree.root_five_impossible p q hp hn hG ⟨h5,h6⟩).elim
  · have hz := actual_six_zero p q hp hn hG
    omega
#print axioms Paper7C61Analytic.integral_parameters_are_c61

theorem check_C61OrbitSix : C61OrbitSix := by
  refine ⟨Paper7C61Orbit.c61_parameters,Paper7C61Orbit.dihedral_orbit_iff,
    Paper7C61Orbit.rotations_card,?_⟩
  intro p q hp hn
  constructor
  · exact integral_parameters_are_c61 p q hp hn
  · rintro ⟨hq,hpRot⟩
    exact Paper7C61Classification.rotations_integral p q hq hpRot
#print axioms Paper7C61Analytic.check_C61OrbitSix

end Paper7C61Analytic
