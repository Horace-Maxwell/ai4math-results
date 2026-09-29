import Research.Backfill.Paper4.Proof.G2DHData
import Research.Backfill.Paper4.Proof.ConcreteCore

/-! Full G2 distance-heredity, assembled from all finite induced-subset certificates.
The general bridge covers arbitrary Set-valued induced subgraphs in the frozen definition.
All acceptance claims are made only by separate compile/audit/checker/replay receipts. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4

namespace G2DistanceHereditary

theorem G2_distanceHereditary : Challenge.IsDistanceHereditary Challenge.G2 :=
  ConcreteDHCertificate.isDistanceHereditary HKOTriameter.G2 HKOTriameter.D2 G2DHData.cut
    HKOTriameter.G2_connected HKOTriameter.G2_dist G2DHData.G2_valid

end G2DistanceHereditary

theorem check_TheoremB_i : Challenge.TheoremB_i :=
  ⟨ConcreteCore.G2_median, G2DistanceHereditary.G2_distanceHereditary,
    ConcreteCore.G2_diam, ConcreteCore.G2_triameter, ConcreteCore.G2_triametral_iff⟩

theorem check_Sec3_medianDH_noQ4 : Challenge.Sec3_medianDH_noQ4 :=
  ⟨Fin 8, inferInstance, Challenge.G2, ConcreteCore.G2_median,
    G2DistanceHereditary.G2_distanceHereditary, HKOTriameter.not_question4_G2⟩

#print axioms G2DistanceHereditary.G2_distanceHereditary
#print axioms check_TheoremB_i
#print axioms check_Sec3_medianDH_noQ4
end CodexPaper4
