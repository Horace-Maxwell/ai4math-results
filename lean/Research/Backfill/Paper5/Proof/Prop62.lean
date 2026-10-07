import Research.Backfill.Paper5.Proof.PartialBrauerThree
import Research.Backfill.Paper5.Proof.BrandtThreeObstruction

set_option autoImplicit false

namespace CodexPaper5.Prop62

open BackfillPaper5

theorem check_Prop62 : Challenge.Prop62 := by
  classical
  constructor
  · exact PartialBrauerThree.magmaIso
  · rintro ⟨α, hα⟩
    apply BrandtThreeObstruction.no_complete_mapping
    exact ⟨_, BrandtThreeObstruction.transport_complete_mapping
      (Challenge.pfMul Challenge.dmul (Challenge.Jr Challenge.Fam.PB 3 2))
      (Challenge.rees0Mul Challenge.delta3)
      PartialBrauerThree.principalBrandtEquiv
      PartialBrauerThree.principalBrandtEquiv_mul α hα⟩

#print axioms CodexPaper5.Prop62.check_Prop62

end CodexPaper5.Prop62
