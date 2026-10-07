import Research.Backfill.Paper5.Proof.SymmetricStep
import Research.Backfill.Paper5.Proof.SymmetricSmall

set_option autoImplicit false

namespace CodexPaper5

open BackfillPaper5

/-- A genuine complete mapping in every degree at least four, by induction. -/
theorem perm_hasCM_of_four_le (n : ℕ) :
    4 ≤ n → Challenge.HasCM (Equiv.Perm (Fin n)) := by
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn
    by_cases hbase : n = 3
    · subst n
      exact SymmetricSmall.perm_four_hasCM
    · exact SymmetricStep.hasCM_succ n (by omega) (ih (by omega))

/-- Full frozen classification, including degree zero. -/
theorem check_SymCMPerm : Challenge.SymCMPerm := by
  intro r
  constructor
  · intro h
    constructor
    · intro hr
      subst r
      exact SymmetricSmall.perm_two_noCM h
    · intro hr
      subst r
      exact SymmetricSmall.perm_three_noCM h
  · rintro ⟨h2, h3⟩
    by_cases h0 : r = 0
    · subst r
      exact SymmetricSmall.perm_zero_hasCM
    by_cases h1 : r = 1
    · subst r
      exact SymmetricSmall.perm_one_hasCM
    exact perm_hasCM_of_four_le r (by omega)

/-- The same full classification for the paper's right-action multiplication. -/
theorem check_SymCM : Challenge.SymCM := by
  intro r
  exact (CMTransport.hasCM_opposite (Equiv.Perm (Fin r))).symm.trans (check_SymCMPerm r)

#print axioms CodexPaper5.perm_hasCM_of_four_le
#print axioms CodexPaper5.check_SymCMPerm
#print axioms CodexPaper5.check_SymCM

end CodexPaper5
