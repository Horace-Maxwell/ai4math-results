import Research.Backfill.Paper8.Challenge
import Research.Backfill.Paper8.Proof.Small.CasesABC
import Research.Backfill.Paper8.Proof.Small.CasesDE

/-!
# Paper 8, Proposition 5.1 (`prop:small`)

`check_Prop_5_1` proves the frozen statement `BackfillPaper8.Challenge.Prop_5_1`, all five cases
(a)–(e), for every choice of the leaves with sign `-1`, from `Lemma_3_2` (a switching is good iff
(S), (L) and (Z) hold) as the only hypothesis. In case (d) the witness is `ε = 1`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge

namespace P8Small

theorem check_Prop_5_1 (h32 : BackfillPaper8.Challenge.Lemma_3_2) :
    BackfillPaper8.Challenge.Prop_5_1 := by
  intro k a hk ha hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hk1 U hU
    exact caseA a h32 hk ha hn hk1 U hU
  · intro hk1 hk0 i0 hi0
    exact caseB a h32 hk ha hk1 hk0 i0 hi0
  · intro hk1 hk0 i0 i1 hi0 hi1
    exact caseC a h32 hk ha hk1 hk0 i0 i1 hi0 hi1
  · intro hk0
    exact ⟨1, Set.mem_insert 1 _, caseD a h32 hk ha hn hk0⟩
  · intro hk0
    exact caseE a h32 hk ha hk0

#print axioms check_Prop_5_1

end P8Small
