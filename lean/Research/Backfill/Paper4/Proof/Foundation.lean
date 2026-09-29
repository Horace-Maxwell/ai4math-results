import Research.Backfill.Paper4.Challenge

/-!
Paper 4: complete frozen arithmetic foundation targets.
Acceptance evidence is maintained separately; this source makes no claim
that compilation, axiom audit, checker or clean replay has passed.
Frozen Challenge SHA-256:
9f1b0c95f35addf03f54c330ea0cd63324154d17e1cc8e707c8bf830da4a0785.

The integer Lemma2 uses the same three-by-three-by-three case structure as
the released natural-number core, but proves the frozen integer statement
directly. No nonnegativity assumption or cast to natural numbers is used.
-/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4

theorem check_Sec5_FP_symm : Challenge.Sec5_FP_symm := by
  constructor
  · intro A B C
    refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro h <;>
      unfold Challenge.FP at * <;> omega
  · intro A B C
    refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro h <;>
      unfold Challenge.FPZ at * <;> omega

theorem check_Sec5_FP_iff_viii : Challenge.Sec5_FP_iff_viii := by
  intro A B C
  unfold Challenge.FP Challenge.BMvii Challenge.BMviiiExtra
  omega

theorem check_Lemma2 : Challenge.Lemma2 := by
  intro D eab eac ebc pa pb pc qa qb qc hab hac hbc fab fac fbc na nb nc
  unfold Challenge.FPZ at fab fac fbc
  rcases fab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases fac with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases fbc with ⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
    omega

#print axioms check_Sec5_FP_symm
#print axioms check_Sec5_FP_iff_viii
#print axioms check_Lemma2

end CodexPaper4
