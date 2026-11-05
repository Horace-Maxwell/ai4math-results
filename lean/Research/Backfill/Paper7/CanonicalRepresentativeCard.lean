import Research.Backfill.Paper7.DihedralLexRepresentative

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
The imported DihedralLexRepresentative and DihedralOrbitBasics are pending source
candidates. This module has not been compiled or accepted. No numerical count is
assumed or evaluated. Different canonical rules are related by an equivalence of
their representative sets, not by an equality of those sets.
-/
set_option autoImplicit false
noncomputable section

namespace Paper7MomentCounts

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7PruningCanonical
open scoped Classical

theorem toLex_le_of_lexLE {b : ℕ} (key : ℕ → ℕ → ℕ) (x y : PQ b)
    (h : LexLE key x y) :
    toLex (fun i => key (x.1 i) (x.2 i)) ≤
      toLex (fun i => key (y.1 i) (y.2 i)) := by
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  change Pi.Lex (· < ·) (· < ·)
    (fun i => key (y.1 i) (y.2 i)) (fun i => key (x.1 i) (x.2 i)) at hlt
  obtain ⟨i, hprefix, hi⟩ := hlt
  exact (not_lt_of_ge (h i (fun j hj => (hprefix j hj).symm))) hi

#print axioms Paper7MomentCounts.toLex_le_of_lexLE

theorem lexLE_keyProfile_eq {b : ℕ} (key : ℕ → ℕ → ℕ) (x y : PQ b)
    (hxy : LexLE key x y) (hyx : LexLE key y x) :
    (fun i => key (x.1 i) (x.2 i)) = (fun i => key (y.1 i) (y.2 i)) := by
  have h := le_antisymm (toLex_le_of_lexLE key x y hxy)
    (toLex_le_of_lexLE key y x hyx)
  change (fun i => key (x.1 i) (x.2 i)) = (fun i => key (y.1 i) (y.2 i)) at h
  exact h

#print axioms Paper7MomentCounts.lexLE_keyProfile_eq

def sameDihedralOrbit (b : ℕ) (x y : PQ b) : Prop :=
  ∃ σ : Fin b → Fin b, IsDihedral b σ ∧ reindex σ x = y

#print axioms Paper7MomentCounts.sameDihedralOrbit

theorem sameDihedralOrbit_refl (b : ℕ) (x : PQ b) : sameDihedralOrbit b x x :=
  ⟨id, dihedral_id b, reindex_id x⟩

#print axioms Paper7MomentCounts.sameDihedralOrbit_refl

theorem sameDihedralOrbit_symm (b : ℕ) (hb : 3 ≤ b) {x y : PQ b}
    (h : sameDihedralOrbit b x y) : sameDihedralOrbit b y x := by
  obtain ⟨σ, hσ, hxy⟩ := h
  obtain ⟨τ, hτ, hστ, _hτσ⟩ := dihedral_inverse b hb σ hσ
  refine ⟨τ, hτ, ?_⟩
  rw [← hxy, reindex_comp, hστ, reindex_id]

#print axioms Paper7MomentCounts.sameDihedralOrbit_symm

theorem sameDihedralOrbit_trans (b : ℕ) (hb : 3 ≤ b) {x y z : PQ b}
    (hxy : sameDihedralOrbit b x y) (hyz : sameDihedralOrbit b y z) :
    sameDihedralOrbit b x z := by
  obtain ⟨σ, hσ, hxy⟩ := hxy
  obtain ⟨τ, hτ, hyz⟩ := hyz
  refine ⟨σ ∘ τ, dihedral_comp b hb σ τ hσ hτ, ?_⟩
  rw [← reindex_comp, hxy, hyz]

#print axioms Paper7MomentCounts.sameDihedralOrbit_trans

def canonicalSubset {b : ℕ} (S : Set (PQ b)) (key : ℕ → ℕ → ℕ)
    (greatest : Bool) : Set (PQ b) :=
  {x | x ∈ S ∧ Canonical key greatest b x}

#print axioms Paper7MomentCounts.canonicalSubset

theorem canonicalSubset_finite {b : ℕ} (S : Set (PQ b))
    (key : ℕ → ℕ → ℕ) (greatest : Bool) (hS : S.Finite) :
    (canonicalSubset S key greatest).Finite :=
  hS.subset (fun _ hx => hx.1)

#print axioms Paper7MomentCounts.canonicalSubset_finite

/-- Injectivity is needed only for the key profiles of members of S. -/
theorem canonical_eq_of_sameDihedralOrbit (b : ℕ) (hb : 3 ≤ b)
    (S : Set (PQ b)) (key : ℕ → ℕ → ℕ) (greatest : Bool)
    (hkey : Set.InjOn (fun x : PQ b => fun i => key (x.1 i) (x.2 i)) S)
    {x y : PQ b} (hx : x ∈ canonicalSubset S key greatest)
    (hy : y ∈ canonicalSubset S key greatest)
    (hxy : sameDihedralOrbit b x y) : x = y := by
  obtain ⟨σ, hσ, hforward⟩ := hxy
  obtain ⟨τ, hτ, hστ, _hτσ⟩ := dihedral_inverse b hb σ hσ
  have hback : reindex τ y = x := by
    rw [← hforward, reindex_comp, hστ, reindex_id]
  have hxlex := hx.2 σ hσ
  have hylex := hy.2 τ hτ
  apply hkey hx.1 hy.1
  cases greatest with
  | false =>
    change LexLE key x (reindex σ x) at hxlex
    change LexLE key y (reindex τ y) at hylex
    rw [hforward] at hxlex
    rw [hback] at hylex
    exact lexLE_keyProfile_eq key x y hxlex hylex
  | true =>
    change LexLE key (reindex σ x) x at hxlex
    change LexLE key (reindex τ y) y at hylex
    rw [hforward] at hxlex
    rw [hback] at hylex
    exact lexLE_keyProfile_eq key x y hylex hxlex

#print axioms Paper7MomentCounts.canonical_eq_of_sameDihedralOrbit

theorem exists_unique_canonical (b : ℕ) (hb : 3 ≤ b)
    (S : Set (PQ b)) (key : ℕ → ℕ → ℕ) (greatest : Bool)
    (hS : ∀ x ∈ S, ∀ σ : Fin b → Fin b,
      IsDihedral b σ → reindex σ x ∈ S)
    (hkey : Set.InjOn (fun x : PQ b => fun i => key (x.1 i) (x.2 i)) S)
    (x : PQ b) (hx : x ∈ S) :
    ∃! y : PQ b, y ∈ canonicalSubset S key greatest ∧ sameDihedralOrbit b x y := by
  obtain ⟨σ, hσ, hcan⟩ := exists_canonical_reindex b hb key greatest x
  have hmem : reindex σ x ∈ canonicalSubset S key greatest :=
    ⟨hS x hx σ hσ, hcan⟩
  have horbit : sameDihedralOrbit b x (reindex σ x) := ⟨σ, hσ, rfl⟩
  refine ⟨reindex σ x, ⟨hmem, horbit⟩, ?_⟩
  intro y hy
  exact canonical_eq_of_sameDihedralOrbit b hb S key greatest hkey hy.1 hmem
    (sameDihedralOrbit_trans b hb (sameDihedralOrbit_symm b hb hy.2) horbit)

#print axioms Paper7MomentCounts.exists_unique_canonical

/-- Each direction chooses the other rule's unique representative in the same orbit. -/
def canonicalSubsetEquiv (b : ℕ) (hb : 3 ≤ b) (S : Set (PQ b))
    (key₁ key₂ : ℕ → ℕ → ℕ) (greatest₁ greatest₂ : Bool)
    (hS : ∀ x ∈ S, ∀ σ : Fin b → Fin b,
      IsDihedral b σ → reindex σ x ∈ S)
    (hkey₁ : Set.InjOn (fun x : PQ b => fun i => key₁ (x.1 i) (x.2 i)) S)
    (hkey₂ : Set.InjOn (fun x : PQ b => fun i => key₂ (x.1 i) (x.2 i)) S) :
    ↥(canonicalSubset S key₁ greatest₁) ≃ ↥(canonicalSubset S key₂ greatest₂) := by
  have ef : ∀ x : ↥(canonicalSubset S key₁ greatest₁),
      ∃ y : ↥(canonicalSubset S key₂ greatest₂), sameDihedralOrbit b x.val y.val := by
    intro x
    obtain ⟨y, hy⟩ :=
      (exists_unique_canonical b hb S key₂ greatest₂ hS hkey₂ x.val x.property.1).exists
    exact ⟨⟨y, hy.1⟩, hy.2⟩
  have eg : ∀ y : ↥(canonicalSubset S key₂ greatest₂),
      ∃ x : ↥(canonicalSubset S key₁ greatest₁), sameDihedralOrbit b y.val x.val := by
    intro y
    obtain ⟨x, hx⟩ :=
      (exists_unique_canonical b hb S key₁ greatest₁ hS hkey₁ y.val y.property.1).exists
    exact ⟨⟨x, hx.1⟩, hx.2⟩
  let f : ↥(canonicalSubset S key₁ greatest₁) → ↥(canonicalSubset S key₂ greatest₂) :=
    fun x => Classical.choose (ef x)
  let g : ↥(canonicalSubset S key₂ greatest₂) → ↥(canonicalSubset S key₁ greatest₁) :=
    fun y => Classical.choose (eg y)
  have hf (x : ↥(canonicalSubset S key₁ greatest₁)) :
      sameDihedralOrbit b x.val (f x).val := Classical.choose_spec (ef x)
  have hg (y : ↥(canonicalSubset S key₂ greatest₂)) :
      sameDihedralOrbit b y.val (g y).val := Classical.choose_spec (eg y)
  refine ⟨f, g, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    exact (canonical_eq_of_sameDihedralOrbit b hb S key₁ greatest₁ hkey₁
      x.property (g (f x)).property
      (sameDihedralOrbit_trans b hb (hf x) (hg (f x)))).symm
  · intro y
    apply Subtype.ext
    exact (canonical_eq_of_sameDihedralOrbit b hb S key₂ greatest₂ hkey₂
      y.property (f (g y)).property
      (sameDihedralOrbit_trans b hb (hg y) (hf (g y)))).symm

#print axioms Paper7MomentCounts.canonicalSubsetEquiv

theorem canonicalSubset_ncard_eq (b : ℕ) (hb : 3 ≤ b) (S : Set (PQ b))
    (key₁ key₂ : ℕ → ℕ → ℕ) (greatest₁ greatest₂ : Bool)
    (hS : ∀ x ∈ S, ∀ σ : Fin b → Fin b,
      IsDihedral b σ → reindex σ x ∈ S)
    (hkey₁ : Set.InjOn (fun x : PQ b => fun i => key₁ (x.1 i) (x.2 i)) S)
    (hkey₂ : Set.InjOn (fun x : PQ b => fun i => key₂ (x.1 i) (x.2 i)) S) :
    (canonicalSubset S key₁ greatest₁).ncard =
      (canonicalSubset S key₂ greatest₂).ncard :=
  Set.ncard_congr' (canonicalSubsetEquiv b hb S key₁ key₂ greatest₁ greatest₂ hS hkey₁ hkey₂)

#print axioms Paper7MomentCounts.canonicalSubset_ncard_eq

end Paper7MomentCounts
