import Research.Backfill.Paper5.Proof.MainAB
import Research.Backfill.Paper5.Proof.PrincipalNonzero

set_option autoImplicit false

namespace CodexPaper5.DiagramCMSufficiency

open BackfillPaper5

/-- A legal diagram is tagged by its actual rank; the inverse forgets only that tag. -/
def rankEquiv (D : Challenge.Fam) (n : ℕ) :
    Challenge.Dset D n ≃ (Σ r : ℕ, Challenge.Jr D n r) where
  toFun x := ⟨Challenge.rank x.val, ⟨x.val, ⟨x.property, rfl⟩⟩⟩
  invFun w := ⟨w.2.val, w.2.property.1⟩
  left_inv x := Subtype.ext rfl
  right_inv w := by
    rcases w with ⟨r, x, hx, hr⟩
    cases hr
    rfl

/-- Use the same rank equivalence for both independently chosen layer bijections.
The transported second bijection is the actual selected diagram product. -/
theorem subsetHasCM_of_rank_layers (D : Challenge.Fam) (n : ℕ)
    (hlayers : ∀ r : ℕ,
      Challenge.SubsetHasCM Challenge.dmul (Challenge.Jr D n r)) :
    Challenge.SubsetHasCM Challenge.dmul (Challenge.Dset D n) := by
  classical
  unfold Challenge.SubsetHasCM at hlayers
  choose α hα hmem hθ using hlayers
  let θ : (r : ℕ) → Challenge.Jr D n r → Challenge.Jr D n r :=
    fun r x => ⟨Challenge.dmul x.val (α r x).val, hmem r x⟩
  have hθbij : ∀ r : ℕ, Function.Bijective (θ r) := hθ
  let e := rankEquiv D n
  let a := Equiv.sigmaCongrRight (fun r => Equiv.ofBijective (α r) (hα r))
  let b := Equiv.sigmaCongrRight (fun r => Equiv.ofBijective (θ r) (hθbij r))
  let A : Challenge.Dset D n → Challenge.Dset D n :=
    fun x => e.symm (a (e x))
  let T : Challenge.Dset D n → Challenge.Dset D n :=
    fun x => e.symm (b (e x))
  have hA : Function.Bijective A :=
    e.symm.bijective.comp (a.bijective.comp e.bijective)
  have hT : Function.Bijective T :=
    e.symm.bijective.comp (b.bijective.comp e.bijective)
  have hval (x : Challenge.Dset D n) :
      (T x).val = Challenge.dmul x.val (A x).val := rfl
  have hproduct (x : Challenge.Dset D n) :
      Challenge.dmul x.val (A x).val ∈ Challenge.Dset D n := by
    rw [← hval x]
    exact (T x).property
  refine ⟨A, hA, hproduct, ?_⟩
  have he : (fun x : Challenge.Dset D n =>
      (⟨Challenge.dmul x.val (A x).val, hproduct x⟩ : Challenge.Dset D n)) = T := by
    funext x
    exact Subtype.ext (hval x).symm
  rw [he]
  exact hT

/-- Nonoccurring ranks have an empty actual carrier; both bijections are vacuous. -/
theorem subsetHasCM_of_not_rankOccurs (D : Challenge.Fam) (n r : ℕ)
    (hocc : ¬ Challenge.RankOccurs D n r) :
    Challenge.SubsetHasCM Challenge.dmul (Challenge.Jr D n r) := by
  have hempty (x : Challenge.Jr D n r) : False :=
    hocc ⟨x.val, x.property.1, x.property.2⟩
  refine ⟨fun x => x, (Equiv.refl (Challenge.Jr D n r)).bijective, ?_, ?_⟩
  · intro x
    exact False.elim (hempty x)
  · constructor
    · intro x _y _hxy
      exact False.elim (hempty x)
    · intro y
      exact False.elim (hempty y)

/-- Every actual rank layer is covered, including rank zero, full rank and empty ranks. -/
theorem rank_layer_hasCM_of_symHasCM (D : Challenge.Fam) (n r : ℕ)
    (hgroup : Challenge.HasCM (Challenge.Sym n)) :
    Challenge.SubsetHasCM Challenge.dmul (Challenge.Jr D n r) := by
  classical
  by_cases hocc : Challenge.RankOccurs D n r
  · have hpf : Challenge.PFHasCM Challenge.dmul (Challenge.Jr D n r) := by
      have hrle : r ≤ n := by
        obtain ⟨x, _hx, hxr⟩ := hocc
        simpa only [hxr] using DiagramUnitGroup.rank_le_n x
      by_cases hrn : r = n
      · subst r
        exact PrincipalMapping.principal_hasCM_of_group D n n hocc hgroup
      · have hlt : r < n := by omega
        cases D with
        | B => exact MainAB.brauer_proper_principal_hasCM n r hocc hlt
        | PB =>
            apply (MainAB.partial_brauer_proper_principal_hasCM_iff n r hocc hlt).mpr
            intro hbad
            exact ((CodexPaper5.check_SymCM n).mp hgroup).2 hbad.1
    exact PrincipalNonzero.subsetHasCM_of_pfHasCM Challenge.dmul
      (Challenge.Jr D n r) hpf
  · exact subsetHasCM_of_not_rankOccurs D n r hocc

/-- Sufficient direction for either actual diagram family and every n, without an
associativity hypothesis or a restriction to occurring ranks. -/
theorem subsetHasCM_of_symHasCM (D : Challenge.Fam) (n : ℕ)
    (hgroup : Challenge.HasCM (Challenge.Sym n)) :
    Challenge.SubsetHasCM Challenge.dmul (Challenge.Dset D n) := by
  exact subsetHasCM_of_rank_layers D n
    (fun r => rank_layer_hasCM_of_symHasCM D n r hgroup)

end CodexPaper5.DiagramCMSufficiency

#print axioms CodexPaper5.DiagramCMSufficiency.rankEquiv
#print axioms CodexPaper5.DiagramCMSufficiency.subsetHasCM_of_rank_layers
#print axioms CodexPaper5.DiagramCMSufficiency.subsetHasCM_of_not_rankOccurs
#print axioms CodexPaper5.DiagramCMSufficiency.rank_layer_hasCM_of_symHasCM
#print axioms CodexPaper5.DiagramCMSufficiency.subsetHasCM_of_symHasCM
