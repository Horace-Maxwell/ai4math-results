import Research.Backfill.Paper4.Proof.F1GDHData
import Research.Backfill.Paper4.Proof.F1HDHData
import Research.Backfill.Paper4.Proof.G2DistanceHereditary

/-! Full distance-heredity of the two HKO Figure 3 graphs and the resulting frozen claims.
Every induced-subset certificate is connected to the graph metric by the general DH bridge.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4

namespace F1DistanceHereditary

theorem F1G_distanceHereditary : Challenge.IsDistanceHereditary Challenge.F1G :=
  ConcreteDHCertificate.isDistanceHereditary HKOTriameter.F1G HKOTriameter.DF1G
    F1GDHData.cut HKOTriameter.F1G_connected HKOTriameter.F1G_dist F1GDHData.F1G_valid

theorem F1H_distanceHereditary : Challenge.IsDistanceHereditary Challenge.F1H :=
  ConcreteDHCertificate.isDistanceHereditary HKOTriameter.F1H HKOTriameter.DF1H
    F1HDHData.cut HKOTriameter.F1H_connected HKOTriameter.F1H_dist F1HDHData.F1H_valid

end F1DistanceHereditary

theorem check_Remark4_i : Challenge.Remark4_i :=
  ⟨F1DistanceHereditary.F1G_distanceHereditary, HKOTriameter.F1G_not_question3',
    F1DistanceHereditary.F1H_distanceHereditary, HKOTriameter.F1H_not_question4,
    G2DistanceHereditary.G2_distanceHereditary, HKOTriameter.not_question4_G2⟩

theorem check_Sec2_classReading : Challenge.Sec2_classReading := by
  constructor
  · intro h
    exact HKOTriameter.F1G_not_question3'
      (h (Fin 6) Challenge.F1G F1DistanceHereditary.F1G_distanceHereditary)
  · intro h
    exact HKOTriameter.F1H_not_question4
      (h (Fin 6) Challenge.F1H F1DistanceHereditary.F1H_distanceHereditary)

#print axioms F1DistanceHereditary.F1G_distanceHereditary
#print axioms F1DistanceHereditary.F1H_distanceHereditary
#print axioms check_Remark4_i
#print axioms check_Sec2_classReading

end CodexPaper4
