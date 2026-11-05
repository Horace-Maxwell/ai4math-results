import Research.Backfill.Paper7.MomentFixedBlockCounts

/-! Pending exact grouping of the actual frozen six-circle action.
The identity keeps the full original labelled cardinality; no numerical
labelled or canonical count is assumed. Twelve actual affine maps are
reduced by explicit conjugacies, with their multiplicities preserved. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalSix
open BackfillPaper7.Challenge.Legacy Paper7MomentCounts
open scoped BigOperators Classical

abbrev B6Dihedral := dihedralSubgroup 6 (by decide)
#print axioms Paper7MomentCanonicalSix.B6Dihedral

def b6FixedCount (σ : B6Dihedral) : ℕ :=
  Fintype.card (CandB1FixedBy 6 42 (by decide) σ)
#print axioms Paper7MomentCanonicalSix.b6FixedCount

def b6NonidentityFixedSum : ℕ :=
  ∑ σ ∈ (Finset.univ : Finset B6Dihedral).erase 1, b6FixedCount σ
#print axioms Paper7MomentCanonicalSix.b6NonidentityFixedSum

def b6IdentityFixedEquiv :
    CandB1FixedBy 6 42 (by decide) (1 : B6Dihedral) ≃ ↥(CandB1 6 42) := by
  letI : MulAction B6Dihedral ↥(CandB1 6 42) := candB1DihedralAction 6 42 (by decide)
  exact { toFun := fun x => x.val
          invFun := fun x => ⟨x, by
            change (1 : B6Dihedral) • x = x
            exact one_smul B6Dihedral x⟩
          left_inv := fun x => by apply Subtype.ext; rfl
          right_inv := fun _ => rfl }
#print axioms Paper7MomentCanonicalSix.b6IdentityFixedEquiv

theorem b6_identity_fixed_count : b6FixedCount 1 = (CandB1 6 42).ncard := by
  rw [b6FixedCount, Fintype.card_congr b6IdentityFixedEquiv]
  exact Set.fintypeCard_eq_ncard _
#print axioms Paper7MomentCanonicalSix.b6_identity_fixed_count

theorem b6_burnside_without_identity :
    (canonB1 6 42).ncard * 12 = (CandB1 6 42).ncard + b6NonidentityFixedSum := by
  have hb := candB1_burnside_two_b 6 42 (by decide) (by decide)
  change (∑ σ : B6Dihedral, b6FixedCount σ) = (canonB1 6 42).ncard * 12 at hb
  have he := Finset.sum_erase_add (Finset.univ : Finset B6Dihedral)
    b6FixedCount (Finset.mem_univ (1 : B6Dihedral))
  change b6NonidentityFixedSum + b6FixedCount 1 = (∑ σ : B6Dihedral, b6FixedCount σ) at he
  rw [b6_identity_fixed_count] at he
  omega
#print axioms Paper7MomentCanonicalSix.b6_burnside_without_identity

abbrev B6Letter := MomentLetter 6 42
#print axioms Paper7MomentCanonicalSix.B6Letter

abbrev B6FixedWords (σ : Equiv.Perm (Fin 6)) :=
  {w : Fin 6 → B6Letter // decodeWord w ∈ CandB1 6 42 ∧ ∀ i, w (σ i) = w i}
#print axioms Paper7MomentCanonicalSix.B6FixedWords

theorem b6_candidate_word_reindex_iff (τ : Equiv.Perm (Fin 6)) (w : Fin 6 → B6Letter) :
    decodeWord (w ∘ τ) ∈ CandB1 6 42 ↔ decodeWord w ∈ CandB1 6 42 := by
  change (Budget 6 42 (reindex τ (decodeWord w)) ∧
    MomentPass false true false 6 42 (reindex τ (decodeWord w))) ↔
    (Budget 6 42 (decodeWord w) ∧ MomentPass false true false 6 42 (decodeWord w))
  exact and_congr (moment_budget_reindex_iff 6 42 τ τ.bijective (decodeWord w))
    (momentPass_reindex_iff false true false 6 42 τ τ.bijective (decodeWord w))
#print axioms Paper7MomentCanonicalSix.b6_candidate_word_reindex_iff

def b6ConjugateWordsEquiv (σ ρ τ : Equiv.Perm (Fin 6))
    (h : ∀ i, τ (σ i) = ρ (τ i)) : B6FixedWords ρ ≃ B6FixedWords σ where
  toFun w := ⟨w.val ∘ τ, (b6_candidate_word_reindex_iff τ w.val).mpr w.property.1, by
    intro i
    change w.val (τ (σ i)) = w.val (τ i)
    rw [h i]
    exact w.property.2 (τ i)⟩
  invFun w := ⟨w.val ∘ τ.symm, (b6_candidate_word_reindex_iff τ.symm w.val).mpr w.property.1, by
    intro i
    have hi : τ.symm (ρ i) = σ (τ.symm i) := by
      apply τ.injective
      simpa only [τ.apply_symm_apply] using (h (τ.symm i)).symm
    change w.val (τ.symm (ρ i)) = w.val (τ.symm i)
    rw [hi]
    exact w.property.2 (τ.symm i)⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    exact congrArg w.val (τ.apply_symm_apply i)
  right_inv w := by
    apply Subtype.ext
    funext i
    exact congrArg w.val (τ.symm_apply_apply i)
#print axioms Paper7MomentCanonicalSix.b6ConjugateWordsEquiv

theorem b6_fixed_count_eq_word_count (σ : B6Dihedral) :
    b6FixedCount σ = Fintype.card (B6FixedWords σ.val) :=
  Fintype.card_congr (candB1FixedWordEquiv 6 42 (by decide) σ)
#print axioms Paper7MomentCanonicalSix.b6_fixed_count_eq_word_count

theorem b6_fixed_count_conjugate (σ ρ : B6Dihedral) (τ : Equiv.Perm (Fin 6))
    (h : ∀ i, τ (σ.val i) = ρ.val (τ i)) : b6FixedCount σ = b6FixedCount ρ := by
  rw [b6_fixed_count_eq_word_count, b6_fixed_count_eq_word_count]
  exact (Fintype.card_congr (b6ConjugateWordsEquiv σ.val ρ.val τ h)).symm
#print axioms Paper7MomentCanonicalSix.b6_fixed_count_conjugate

abbrev b6Rotation (c : Fin 6) : B6Dihedral := dihedralCardRotation 3 (by decide) c
#print axioms Paper7MomentCanonicalSix.b6Rotation

abbrev b6Reflection (c : Fin 6) : B6Dihedral := dihedralCardReflection 3 (by decide) c
#print axioms Paper7MomentCanonicalSix.b6Reflection

theorem b6_rotation_zero : b6Rotation 0 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  change i + 0 = i
  exact add_zero i
#print axioms Paper7MomentCanonicalSix.b6_rotation_zero

theorem b6_rotation_five_count : b6FixedCount (b6Rotation 5) = b6FixedCount (b6Rotation 1) := by
  apply b6_fixed_count_conjugate _ _ (b6Reflection 0).val
  intro i
  fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalSix.b6_rotation_five_count

theorem b6_rotation_four_count : b6FixedCount (b6Rotation 4) = b6FixedCount (b6Rotation 2) := by
  apply b6_fixed_count_conjugate _ _ (b6Reflection 0).val
  intro i
  fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalSix.b6_rotation_four_count

def b6OddReflectionConjugator : Equiv.Perm (Fin 6) :=
  { toFun := ![0,3,1,2,5,4]
    invFun := ![0,2,3,1,5,4]
    left_inv := by intro i; fin_cases i <;> rfl
    right_inv := by intro i; fin_cases i <;> rfl }
#print axioms Paper7MomentCanonicalSix.b6OddReflectionConjugator

theorem b6_reflection_one_count : b6FixedCount (b6Reflection 1) = b6FixedCount (b6Rotation 3) := by
  apply b6_fixed_count_conjugate _ _ b6OddReflectionConjugator
  intro i
  fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalSix.b6_reflection_one_count

theorem b6_reflection_three_count : b6FixedCount (b6Reflection 3) = b6FixedCount (b6Reflection 1) := by
  apply b6_fixed_count_conjugate _ _ (b6Rotation 2).val
  intro i
  fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalSix.b6_reflection_three_count

theorem b6_reflection_five_count : b6FixedCount (b6Reflection 5) = b6FixedCount (b6Reflection 1) := by
  apply b6_fixed_count_conjugate _ _ (b6Rotation 1).val
  intro i
  fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalSix.b6_reflection_five_count

theorem b6_reflection_two_count : b6FixedCount (b6Reflection 2) = b6FixedCount (b6Reflection 0) := by
  apply b6_fixed_count_conjugate _ _ (b6Rotation 2).val
  intro i
  fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalSix.b6_reflection_two_count

theorem b6_reflection_four_count : b6FixedCount (b6Reflection 4) = b6FixedCount (b6Reflection 0) := by
  apply b6_fixed_count_conjugate _ _ (b6Rotation 1).val
  intro i
  fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalSix.b6_reflection_four_count

theorem b6_affine_fixed_sum :
    (∑ σ : B6Dihedral, b6FixedCount σ) =
      (∑ c : Fin 6, b6FixedCount (b6Rotation c)) +
      (∑ c : Fin 6, b6FixedCount (b6Reflection c)) := by
  calc
    (∑ σ : B6Dihedral, b6FixedCount σ) =
        ∑ c : Fin 6 ⊕ Fin 6, b6FixedCount (dihedralCardEncode 3 (by decide) c) :=
      ((dihedralCardAffineEquiv 3 (by decide)).sum_comp b6FixedCount).symm
    _ = _ := Fintype.sum_sum_type _
#print axioms Paper7MomentCanonicalSix.b6_affine_fixed_sum

theorem b6_nonidentity_grouped :
    b6NonidentityFixedSum = 2 * b6FixedCount (b6Rotation 1) +
      2 * b6FixedCount (b6Rotation 2) + 4 * b6FixedCount (b6Rotation 3) +
      3 * b6FixedCount (b6Reflection 0) := by
  have h := b6_affine_fixed_sum
  rw [Fin.sum_univ_six, Fin.sum_univ_six, b6_rotation_zero,
    b6_rotation_five_count, b6_rotation_four_count, b6_reflection_three_count,
    b6_reflection_five_count, b6_reflection_two_count, b6_reflection_four_count,
    b6_reflection_one_count] at h
  have he := Finset.sum_erase_add (Finset.univ : Finset B6Dihedral)
    b6FixedCount (Finset.mem_univ (1 : B6Dihedral))
  change b6NonidentityFixedSum + b6FixedCount 1 = (∑ σ : B6Dihedral, b6FixedCount σ) at he
  omega
#print axioms Paper7MomentCanonicalSix.b6_nonidentity_grouped

end Paper7MomentCanonicalSix
