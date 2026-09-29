import Research.Backfill.Paper4.Proof.ConcreteCore
import Research.HKOTriameterDH

/-! Three complete frozen claims using the concrete graph certificates.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4

theorem check_Remark4_ii : Challenge.Remark4_ii := by
  have hd : ∀ u v, Challenge.F1H.dist u v = HKOTriameter.DF1H u v :=
    HKOTriameter.F1H_dist
  have hdiam : Challenge.F1H.diam = 2 := HKOTriameter.F1H_diam
  have htri : Challenge.triameter Challenge.F1H = 6 := HKOTriameter.F1H_triameter
  refine ⟨hdiam, htri, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v w
    simp only [Challenge.IsTriametral, htri, Challenge.triDist, hd]
    revert u v w
    decide +kernel
  · rw [hd]
    decide
  · rw [hd]
    decide
  · rw [hd]
    decide
  · unfold Challenge.IsDiametral
    rw [hdiam, hd]
    decide
  · intro z
    simp only [Challenge.IsTriametral, htri, Challenge.triDist, hd]
    revert z
    decide

theorem check_Sec8_open : Challenge.Sec8_open := by
  rcases check_TheoremA_ii with ⟨_, _, _, _, _, _, hQ4, _⟩
  rcases check_TheoremB_ii with ⟨_, _, _, _, _, _, _, _, _, _, _, hQ3, _, _⟩
  have hc : Challenge.G2.Connected := HKOTriameter.G2_connected
  exact ⟨hQ4, check_Sec2_Q3_imp_Q3' (Fin 8) Challenge.G2 hc hQ3⟩

theorem check_Sec2_problem2_altReading : Challenge.Sec2_problem2_altReading := by
  intro h
  have hmedian : Challenge.IsMedian Challenge.G1 := check_TheoremA_i.1
  rcases check_TheoremA_ii with ⟨_, _, _, _, hnot, _, _, _⟩
  exact hnot (h (Fin 8) Challenge.G1 hmedian)

#print axioms check_Remark4_ii
#print axioms check_Sec8_open
#print axioms check_Sec2_problem2_altReading

end CodexPaper4
