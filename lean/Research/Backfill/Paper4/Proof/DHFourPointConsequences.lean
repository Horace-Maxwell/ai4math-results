import Research.Backfill.Paper4.Proof.DHFourPoint
import Research.Backfill.Paper4.Proof.TheoremCFP

/-! Full frozen DH consequences, using the full DH-to-four-point theorem.
No four-point assumption is added to these three frozen goals.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4

theorem check_TheoremC_i : Challenge.TheoremC_i := by
  intro V _ G hd
  exact (check_TheoremC_FP V G hd.1 (check_BandeltMulder_DH_fourPoint V G hd)).1

theorem check_TheoremC_ii : Challenge.TheoremC_ii := by
  intro V _ G hd
  obtain ⟨_, h34, h3s, hp4⟩ :=
    check_TheoremC_FP V G hd.1 (check_BandeltMulder_DH_fourPoint V G hd)
  refine ⟨h34, hp4, h3s, ?_⟩
  exact hp4.imp id (check_Sec2_Q4_imp_Q4' V G hd.1)

theorem check_Sec3_DH_noQ4_imp_Q3 : Challenge.Sec3_DH_noQ4_imp_Q3 := by
  intro V _ G hd hn4
  exact (check_TheoremC_ii V G hd).1.resolve_right hn4

#print axioms check_TheoremC_i
#print axioms check_TheoremC_ii
#print axioms check_Sec3_DH_noQ4_imp_Q3
end CodexPaper4
