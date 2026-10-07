import Research.Backfill.Paper5.Proof.PrincipalMapping
import Research.Backfill.Paper5.Proof.BrauerCyclePermutation
import Research.Backfill.Paper5.Proof.BrauerParity
import Research.Backfill.Paper5.Proof.PartialBrauerParity
import Research.Backfill.Paper5.Proof.SymmetricClassification
import Research.Backfill.Paper5.Proof.Prop62
import Research.Backfill.Paper5.Proof.ReesCycle

set_option autoImplicit false

namespace CodexPaper5.MainAB

open BackfillPaper5

section Proofs

open Classical

theorem group_hasCM_of_not_small (r : ℕ) (hr : ¬ (r = 2 ∨ r = 3)) :
    Challenge.HasCM (Challenge.Sym r) := by
  apply (CodexPaper5.check_SymCM r).mpr
  exact ⟨fun h => hr (Or.inl h), fun h => hr (Or.inr h)⟩

/-- All actual proper Brauer rank layers, including the odd small-rank branch. -/
theorem brauer_proper_principal_hasCM (n r : ℕ)
    (hocc : Challenge.RankOccurs Challenge.Fam.B n r) (hrn : r < n) :
    Challenge.PFHasCM Challenge.dmul (Challenge.Jr Challenge.Fam.B n r) := by
  by_cases hr : r = 2 ∨ r = 3
  · rcases Nat.even_or_odd (Nat.card (Challenge.HSub Challenge.Fam.B n r)) with
      heven | hodd
    · exact PrincipalMapping.principal_hasCM_of_even Challenge.Fam.B n r hocc hr heven
    · obtain ⟨l, hl⟩ :=
        (DiagramRanksOccurring.rankOccurs_iff_exists_half Challenge.Fam.B n r).mp hocc
      have hpar : n % 2 = r % 2 := (DiagramRanksOccurring.brauer_half_parity hl).symm
      have hodd' : Odd (Challenge.Hr Challenge.Fam.B n r).ncard := by
        simpa only [Nat.card_coe_set_eq] using hodd
      obtain ⟨hgap, hchoose⟩ := BrauerParity.odd_gap_and_choose n r hr hrn hpar hodd'
      obtain ⟨ρ, hρ, hcycle⟩ :=
        BrauerCyclePermutation.exists_cycle_permutation hr hrn hpar hgap hchoose
      let _ : Nonempty (Challenge.HSub Challenge.Fam.B n r) :=
        PrincipalMapping.halfSubtype_nonempty Challenge.Fam.B n r hocc
      apply (PrincipalMapping.principal_hasCM_iff_rees Challenge.Fam.B n r hocc).mpr
      exact (CodexPaper5.check_Lemma44 r hr (Challenge.HSub Challenge.Fam.B n r)
        (Challenge.sandSub Challenge.Fam.B n r)
        (PrincipalMapping.sandSub_diagonal Challenge.Fam.B n r) ρ hρ hcycle).2.2
  · exact PrincipalMapping.principal_hasCM_of_group Challenge.Fam.B n r hocc
      (group_hasCM_of_not_small r hr)

/-- Both existence directions on every proper actual partial-Brauer rank layer. -/
theorem partial_brauer_proper_principal_hasCM_iff (n r : ℕ)
    (hocc : Challenge.RankOccurs Challenge.Fam.PB n r) (hrn : r < n) :
    Challenge.PFHasCM Challenge.dmul (Challenge.Jr Challenge.Fam.PB n r) ↔
      ¬ (n = 3 ∧ r = 2) := by
  constructor
  · intro hcm hbad
    rcases hbad with ⟨rfl, rfl⟩
    exact Prop62.check_Prop62.2 hcm
  · intro hgood
    by_cases hr : r = 2 ∨ r = 3
    · have hn : 4 ≤ n := by
        by_contra hsmall
        have hbad : n = 3 ∧ r = 2 := by
          rcases hr with hr | hr <;> omega
        exact hgood hbad
      have heven : Even (Nat.card (Challenge.HSub Challenge.Fam.PB n r)) := by
        simpa only [Nat.card_coe_set_eq] using
          PartialBrauerParity.even_ncard_Hr_PB n r hn hr hrn
      exact PrincipalMapping.principal_hasCM_of_even Challenge.Fam.PB n r hocc hr heven
    · exact PrincipalMapping.principal_hasCM_of_group Challenge.Fam.PB n r hocc
        (group_hasCM_of_not_small r hr)

theorem check_Thm11a : Challenge.Thm11a := by
  intro n _hn x hx hproper
  have hJ : Challenge.JClass Challenge.dmul (Challenge.B n) x =
      Challenge.Jr Challenge.Fam.B n (Challenge.rank x) :=
    PrincipalMapping.jClass_eq_Jr Challenge.Fam.B n x hx
  rw [hJ]
  exact brauer_proper_principal_hasCM n (Challenge.rank x) ⟨x, hx, rfl⟩
    (PrincipalMapping.proper_rank_lt Challenge.Fam.B n x hx hproper)

theorem check_Thm11b : Challenge.Thm11b := by
  intro n _hn x hx hproper
  have hJ : Challenge.JClass Challenge.dmul (Challenge.PB n) x =
      Challenge.Jr Challenge.Fam.PB n (Challenge.rank x) :=
    PrincipalMapping.jClass_eq_Jr Challenge.Fam.PB n x hx
  rw [hJ]
  refine ⟨partial_brauer_proper_principal_hasCM_iff n (Challenge.rank x)
    ⟨x, hx, rfl⟩ (PrincipalMapping.proper_rank_lt Challenge.Fam.PB n x hx hproper), ?_⟩
  intro hn hrank
  subst n
  rw [hrank]
  exact Prop62.check_Prop62.1

end Proofs

#print axioms CodexPaper5.MainAB.group_hasCM_of_not_small
#print axioms CodexPaper5.MainAB.brauer_proper_principal_hasCM
#print axioms CodexPaper5.MainAB.partial_brauer_proper_principal_hasCM_iff
#print axioms CodexPaper5.MainAB.check_Thm11a
#print axioms CodexPaper5.MainAB.check_Thm11b

end CodexPaper5.MainAB
