import Research.Backfill.Paper5.Proof.DiagramPrincipalFactor
import Research.Backfill.Paper5.Proof.DiagramJClasses
import Research.Backfill.Paper5.Proof.DiagramUnitGroup
import Research.Backfill.Paper5.Proof.DiagramRanksOccurring
import Research.Backfill.Paper5.Proof.BrandtThreeObstruction
import Research.Backfill.Paper5.Proof.ReesEven

set_option autoImplicit false

namespace CodexPaper5.PrincipalMapping

open BackfillPaper5

section Proofs

open Classical

/-- The actual Green class of a legal diagram is its actual rank layer. -/
theorem jClass_eq_Jr (D : Challenge.Fam) (n : ℕ)
    (x : Challenge.Pt n → Challenge.Pt n) (hx : x ∈ Challenge.Dset D n) :
    Challenge.JClass Challenge.dmul (Challenge.Dset D n) x =
      Challenge.Jr D n (Challenge.rank x) := by
  ext y
  constructor
  · rintro ⟨hy, hxy⟩
    exact ⟨hy, (DiagramJClasses.rank_eq_of_JRel hx hy hxy).symm⟩
  · rintro ⟨hy, hr⟩
    exact ⟨hy, DiagramJClasses.JRel_of_rank_eq hx hy hr.symm⟩

/-- Properness in the frozen Green relation forces a strictly smaller rank. -/
theorem proper_rank_lt (D : Challenge.Fam) (n : ℕ)
    (x : Challenge.Pt n → Challenge.Pt n) (hx : x ∈ Challenge.Dset D n)
    (hproper : ¬ Challenge.JRel Challenge.dmul (Challenge.Dset D n) x
      (Challenge.idD n)) : Challenge.rank x < n := by
  have hle := DiagramUnitGroup.rank_le_n x
  have hne : Challenge.rank x ≠ n := by
    intro heq
    apply hproper
    apply DiagramJClasses.JRel_of_rank_eq hx (DiagramUnitGroup.idD_mem_Jr D n).1
    exact heq.trans (DiagramUnitGroup.rank_idD n).symm
  omega

theorem halfSubtype_nonempty (D : Challenge.Fam) (n r : ℕ)
    (hocc : Challenge.RankOccurs D n r) : Nonempty (Challenge.HSub D n r) := by
  obtain ⟨l, hl⟩ := (DiagramRanksOccurring.rankOccurs_iff_exists_half D n r).mp hocc
  exact ⟨⟨l, hl⟩⟩

theorem sandSub_diagonal (D : Challenge.Fam) (n r : ℕ)
    (l : Challenge.HSub D n r) : Challenge.sandSub D n r l l = some 1 := by
  rw [DiagramPrincipalFactor.sandSub_eq_some_of_compat l l
    (HalfDiagonal.compat_of_same_free rfl),
    HalfDiagonal.pSand_eq_one_of_same_free l.property l.property rfl]

/-- The inverse of the same equivalence also preserves the actual operations. -/
theorem inverse_preserves_operation {A B : Type*} (opA : A → A → A)
    (opB : B → B → B) (e : A ≃ B)
    (hm : ∀ x y, e (opA x y) = opB (e x) (e y)) (u v : B) :
    e.symm (opB u v) = opA (e.symm u) (e.symm v) := by
  apply e.injective
  simpa only [e.apply_symm_apply] using (hm (e.symm u) (e.symm v)).symm

/-- Both complete-mapping existence directions use one operation-preserving equivalence. -/
theorem exists_complete_mapping_iff {A B : Type*} (opA : A → A → A)
    (opB : B → B → B) (e : A ≃ B)
    (hm : ∀ x y, e (opA x y) = opB (e x) (e y)) :
    (∃ α : A → A, Challenge.IsCompleteMapping opA α) ↔
      ∃ β : B → B, Challenge.IsCompleteMapping opB β := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨_, BrandtThreeObstruction.transport_complete_mapping opA opB e hm α hα⟩
  · rintro ⟨β, hβ⟩
    exact ⟨_, BrandtThreeObstruction.transport_complete_mapping opB opA e.symm
      (inverse_preserves_operation opA opB e hm) β hβ⟩

theorem principal_hasCM_iff_rees (D : Challenge.Fam) (n r : ℕ)
    (hocc : Challenge.RankOccurs D n r) :
    Challenge.PFHasCM Challenge.dmul (Challenge.Jr D n r) ↔
      ∃ α, Challenge.IsCompleteMapping
        (Challenge.rees0Mul (Challenge.sandSub D n r)) α := by
  exact exists_complete_mapping_iff
    (Challenge.pfMul Challenge.dmul (Challenge.Jr D n r))
    (Challenge.rees0Mul (Challenge.sandSub D n r))
    (DiagramPrincipalFactor.principalEquiv D n r hocc)
    (DiagramPrincipalFactor.principalEquiv_mul D n r hocc)

/-- A complete mapping of the actual maximal group gives one of the actual principal factor. -/
theorem principal_hasCM_of_group (D : Challenge.Fam) (n r : ℕ)
    (hocc : Challenge.RankOccurs D n r) (hgroup : Challenge.HasCM (Challenge.Sym r)) :
    Challenge.PFHasCM Challenge.dmul (Challenge.Jr D n r) := by
  let _ : Nonempty (Challenge.HSub D n r) := halfSubtype_nonempty D n r hocc
  obtain ⟨L, hL⟩ := ReesEven.exists_latin (Challenge.HSub D n r)
  obtain ⟨φ, hφ⟩ := hgroup
  apply (principal_hasCM_iff_rees D n r hocc).mpr
  exact ⟨_, CodexPaper5.check_Lemma41 r (Challenge.HSub D n r)
    (Challenge.sandSub D n r) L φ (sandSub_diagonal D n r) hL hφ⟩

/-- The even actual index-set branch uses the complete small-group Rees theorem. -/
theorem principal_hasCM_of_even (D : Challenge.Fam) (n r : ℕ)
    (hocc : Challenge.RankOccurs D n r) (hr : r = 2 ∨ r = 3)
    (heven : Even (Nat.card (Challenge.HSub D n r))) :
    Challenge.PFHasCM Challenge.dmul (Challenge.Jr D n r) := by
  let _ : Nonempty (Challenge.HSub D n r) := halfSubtype_nonempty D n r hocc
  apply (principal_hasCM_iff_rees D n r hocc).mpr
  exact ((CodexPaper5.check_Lemma43 r hr (Challenge.HSub D n r)
    (Challenge.sandSub D n r) (sandSub_diagonal D n r)).2 heven).2

end Proofs

#print axioms CodexPaper5.PrincipalMapping.jClass_eq_Jr
#print axioms CodexPaper5.PrincipalMapping.proper_rank_lt
#print axioms CodexPaper5.PrincipalMapping.halfSubtype_nonempty
#print axioms CodexPaper5.PrincipalMapping.sandSub_diagonal
#print axioms CodexPaper5.PrincipalMapping.inverse_preserves_operation
#print axioms CodexPaper5.PrincipalMapping.exists_complete_mapping_iff
#print axioms CodexPaper5.PrincipalMapping.principal_hasCM_iff_rees
#print axioms CodexPaper5.PrincipalMapping.principal_hasCM_of_group
#print axioms CodexPaper5.PrincipalMapping.principal_hasCM_of_even

end CodexPaper5.PrincipalMapping
