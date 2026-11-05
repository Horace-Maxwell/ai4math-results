import Research.Backfill.Paper7.SunSchwenkCycleData
import Research.Backfill.Paper7.UnicyclicSchwenkIdentity

/-! Sun instance of the exact frozen unicyclic Schwenk contract.
The general identity and cycle-data modules are actual development successes.
This new wrapper is uncompiled and adds no hypothesis to the frozen contract. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Paper7SunSchwenk
open SimpleGraph BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem check_SunSchwenkIdentity :
    BackfillPaper7.Challenge.Legacy.Algebra.SunSchwenkIdentity := by
  intro b L hb u v huv
  obtain ⟨r, c, hc, hlen, hedge, hsupport⟩ := sun_cycle_edge_witness b L hb u v huv
  let fV : Fintype (SunV b L) := inferInstance
  let dV : DecidableEq (SunV b L) := inferInstance
  let aG : DecidableRel (sunGraph b L).Adj := inferInstance
  have h := @Paper7UnicyclicSchwenk.check_UnicyclicSchwenkIdentity
    (SunV b L) fV dV (sunGraph b L) aG b (sun_unicyclic b L hb)
    r c hc hlen (Sum.inl u) (Sum.inl v) hedge
  let S : Set (SunV b L) := {z | z ∈ c.support}
  let C : Set (SunV b L) := sunCycleVertices b L
  let e : {z : SunV b L // z ∉ S} ≃ {z : SunV b L // z ∉ C} :=
    Equiv.subtypeEquivRight (fun z => not_congr (Set.ext_iff.mp hsupport z))
  let fS : Fintype {z : SunV b L // z ∉ S} := inferInstance
  let fC : Fintype {z : SunV b L // z ∉ C} := inferInstance
  let dS : DecidableEq {z : SunV b L // z ∉ S} := inferInstance
  let dC : DecidableEq {z : SunV b L // z ∉ C} := inferInstance
  let aS : DecidableRel (deleteVertices (sunGraph b L) S).Adj := inferInstance
  let aC : DecidableRel (deleteVertices (sunGraph b L) C).Adj := inferInstance
  have hcycle := @Paper7UnicyclicSchwenk.graphPhi_equiv
    {z : SunV b L // z ∉ S} {z : SunV b L // z ∉ C}
    fS fC dS dC (deleteVertices (sunGraph b L) S)
    (deleteVertices (sunGraph b L) C) aS aC e (fun _ _ => Iff.rfl)
  refine (Paper7UnicyclicSchwenk.graphPhi_instances_eq _ fV _ dV (sunGraph b L)).trans ?_
  refine h.trans ?_
  apply congrArg₂ (fun A B : Polynomial ℤ => A - B)
  · apply congrArg₂ (fun A B : Polynomial ℤ => A - B)
    · exact Paper7UnicyclicSchwenk.graphPhi_instances_eq _ _ _ _ _
    · exact Paper7UnicyclicSchwenk.graphPhi_instances_eq _ _ _ _ _
  · apply congrArg (fun z : Polynomial ℤ => 2 * z)
    exact (Paper7UnicyclicSchwenk.graphPhi_instances_eq _ fS _ dS
      (deleteVertices (sunGraph b L) S)).trans
      (hcycle.trans (Paper7UnicyclicSchwenk.graphPhi_instances_eq fC _ dC _
        (deleteVertices (sunGraph b L) C)))
#print axioms Paper7SunSchwenk.check_SunSchwenkIdentity

end Paper7SunSchwenk
