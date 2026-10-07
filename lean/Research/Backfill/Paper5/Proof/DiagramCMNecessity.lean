import Research.Backfill.Paper5.Proof.DiagramUnitGroup

set_option autoImplicit false

namespace CodexPaper5.DiagramCMNecessity

open BackfillPaper5
open scoped BigOperators

/-- The same two bijections and the two pointwise bounds force both maps to preserve rank. -/
theorem finite_rank_preservation {M : Type*} [Finite M]
    (ρ : M → ℕ) (α θ : M → M)
    (hα : Function.Bijective α) (hθ : Function.Bijective θ)
    (hL : ∀ x, ρ (θ x) ≤ ρ x) (hR : ∀ x, ρ (θ x) ≤ ρ (α x)) :
    (∀ x, ρ (θ x) = ρ x) ∧ (∀ x, ρ (α x) = ρ x) := by
  classical
  let _ : Fintype M := Fintype.ofFinite M
  have hleft : ∀ x, ρ (θ x) = ρ x := by
    intro x
    exact (Finset.sum_eq_sum_iff_of_le
      (s := Finset.univ) (f := fun z => ρ (θ z)) (g := ρ)
      (fun z _hz => hL z)).mp (hθ.sum_comp ρ) x (Finset.mem_univ x)
  have hright : ∀ x, ρ (θ x) = ρ (α x) := by
    intro x
    exact (Finset.sum_eq_sum_iff_of_le
      (s := Finset.univ) (f := fun z => ρ (θ z)) (g := fun z => ρ (α z))
      (fun z _hz => hR z)).mp
        ((hθ.sum_comp ρ).trans (hα.sum_comp ρ).symm) x (Finset.mem_univ x)
  exact ⟨hleft, fun x => (hright x).symm.trans (hleft x)⟩

def embed_rank (D : Challenge.Fam) (n r : ℕ) (x : Challenge.Jr D n r) :
    Challenge.Dset D n := ⟨x.val, x.property.1⟩

/-- This is the original map restricted to the actual rank layer, including empty layers. -/
def restrict_rank (D : Challenge.Fam) (n r : ℕ)
    (f : Challenge.Dset D n → Challenge.Dset D n)
    (hf : ∀ x, Challenge.rank (f x).val = Challenge.rank x.val)
    (x : Challenge.Jr D n r) : Challenge.Jr D n r :=
  ⟨(f (embed_rank D n r x)).val,
    ⟨(f (embed_rank D n r x)).property, (hf (embed_rank D n r x)).trans x.property.2⟩⟩

theorem restrict_rank_val (D : Challenge.Fam) (n r : ℕ)
    (f : Challenge.Dset D n → Challenge.Dset D n)
    (hf : ∀ x, Challenge.rank (f x).val = Challenge.rank x.val)
    (x : Challenge.Jr D n r) :
    (restrict_rank D n r f hf x).val = (f (embed_rank D n r x)).val := rfl

/-- Surjectivity uses the original preimage and proves that it has the required rank. -/
theorem restrict_rank_bijective (D : Challenge.Fam) (n r : ℕ)
    (f : Challenge.Dset D n → Challenge.Dset D n)
    (hf : ∀ x, Challenge.rank (f x).val = Challenge.rank x.val)
    (hbij : Function.Bijective f) : Function.Bijective (restrict_rank D n r f hf) := by
  constructor
  · intro x y hxy
    have he : f (embed_rank D n r x) = f (embed_rank D n r y) :=
      Subtype.ext (congrArg (fun u : Challenge.Jr D n r => u.val) hxy)
    exact Subtype.ext (congrArg (fun u : Challenge.Dset D n => u.val) (hbij.1 he))
  · intro y
    obtain ⟨x, hxy⟩ := hbij.2 (embed_rank D n r y)
    have hxr : Challenge.rank x.val = r :=
      (hf x).symm.trans
        ((congrArg (fun z : Challenge.Dset D n => Challenge.rank z.val) hxy).trans y.property.2)
    let z : Challenge.Jr D n r := ⟨x.val, ⟨x.property, hxr⟩⟩
    have hz : embed_rank D n r z = x := Subtype.ext rfl
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change (f (embed_rank D n r z)).val = y.val
    rw [hz]
    exact congrArg Subtype.val hxy

/-- Both original complete-mapping bijections restrict to every actual rank layer. -/
theorem subsetHasCM_rank (D : Challenge.Fam) (n r : ℕ) :
    Challenge.SubsetHasCM Challenge.dmul (Challenge.Dset D n) →
      Challenge.SubsetHasCM Challenge.dmul (Challenge.Jr D n r) := by
  rintro ⟨α, hα, h, hθ⟩
  let θ : Challenge.Dset D n → Challenge.Dset D n :=
    fun x => ⟨Challenge.dmul x.val (α x).val, h x⟩
  have hθbij : Function.Bijective θ := hθ
  have hpb : ∀ x : Challenge.Dset D n, Challenge.IsPB x.val := by
    intro x
    exact DiagramExtraction.isPB_of_mem_Jr (D := D) (r := Challenge.rank x.val) ⟨x.property, rfl⟩
  obtain ⟨hθrank, hαrank⟩ := finite_rank_preservation
    (fun x : Challenge.Dset D n => Challenge.rank x.val) α θ hα hθbij
    (fun x => DiagramRank.rank_dmul_le_left (hpb x) (hpb (α x)))
    (fun x => DiagramRank.rank_dmul_le_right (hpb x) (hpb (α x)))
  let β := restrict_rank D n r α hαrank
  let ν := restrict_rank D n r θ hθrank
  have hβ : Function.Bijective β := restrict_rank_bijective D n r α hαrank hα
  have hν : Function.Bijective ν := restrict_rank_bijective D n r θ hθrank hθbij
  have hproduct : ∀ u : Challenge.Jr D n r,
      Challenge.dmul u.val (β u).val ∈ Challenge.Jr D n r := by
    intro u
    exact ⟨h (embed_rank D n r u), (hθrank (embed_rank D n r u)).trans u.property.2⟩
  refine ⟨β, hβ, hproduct, ?_⟩
  have he : (fun u : Challenge.Jr D n r =>
      (⟨Challenge.dmul u.val (β u).val, hproduct u⟩ : Challenge.Jr D n r)) = ν := by
    funext u
    exact Subtype.ext rfl
  rw [he]
  exact hν

/-- The same unit equivalence and its actual multiplication law send the full-rank mapping
and its selected-product mapping to the two genuine symmetric-group bijections. -/
theorem unit_subsetHasCM_implies_symHasCM (D : Challenge.Fam) (n : ℕ) :
    Challenge.SubsetHasCM Challenge.dmul (Challenge.Jr D n n) →
      Challenge.HasCM (Challenge.Sym n) := by
  rintro ⟨β, hβ, h, hν⟩
  let ν : Challenge.Jr D n n → Challenge.Jr D n n :=
    fun u => ⟨Challenge.dmul u.val (β u).val, h u⟩
  have hνbij : Function.Bijective ν := hν
  let e := DiagramUnitGroup.unitEquiv D n
  let γ : Challenge.Sym n → Challenge.Sym n := fun g => e.symm (β (e g))
  have hγ : Function.Bijective γ := e.symm.bijective.comp (hβ.comp e.bijective)
  have hunit (g : Challenge.Sym n) : e (g * γ g) = ν (e g) := by
    apply Subtype.ext
    calc
      (e (g * γ g)).val = Challenge.dmul (e g).val (e (γ g)).val :=
        DiagramUnitGroup.unitDiagram_mul D n g (γ g)
      _ = Challenge.dmul (e g).val (β (e g)).val :=
        congrArg (fun u : Challenge.Jr D n n => Challenge.dmul (e g).val u.val)
          (e.apply_symm_apply (β (e g)))
      _ = (ν (e g)).val := rfl
  have hproduct (g : Challenge.Sym n) : g * γ g = e.symm (ν (e g)) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact hunit g
  refine ⟨γ, hγ, ?_⟩
  have he : (fun g : Challenge.Sym n => g * γ g) =
      (fun g : Challenge.Sym n => e.symm (ν (e g))) := funext hproduct
  rw [he]
  exact e.symm.bijective.comp (hνbij.comp e.bijective)

/-- This necessary implication holds for either family and every n, including n=0. -/
theorem subsetHasCM_implies_symHasCM (D : Challenge.Fam) (n : ℕ) :
    Challenge.SubsetHasCM Challenge.dmul (Challenge.Dset D n) →
      Challenge.HasCM (Challenge.Sym n) := by
  intro h
  exact unit_subsetHasCM_implies_symHasCM D n (subsetHasCM_rank D n n h)

end CodexPaper5.DiagramCMNecessity

#print axioms CodexPaper5.DiagramCMNecessity.finite_rank_preservation
#print axioms CodexPaper5.DiagramCMNecessity.embed_rank
#print axioms CodexPaper5.DiagramCMNecessity.restrict_rank
#print axioms CodexPaper5.DiagramCMNecessity.restrict_rank_val
#print axioms CodexPaper5.DiagramCMNecessity.restrict_rank_bijective
#print axioms CodexPaper5.DiagramCMNecessity.subsetHasCM_rank
#print axioms CodexPaper5.DiagramCMNecessity.unit_subsetHasCM_implies_symHasCM
#print axioms CodexPaper5.DiagramCMNecessity.subsetHasCM_implies_symHasCM
