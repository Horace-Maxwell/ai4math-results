import Research.Backfill.Paper7.MomentB4NonidentityBurnside

/-! Source-only: all eight actual affine dihedral maps are retained. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge.Legacy
open Paper7MomentCounts
open scoped BigOperators Classical

abbrev B4Letter := MomentLetter 4 41
#print axioms Paper7MomentCanonicalNumeric.B4Letter

abbrev B4FixedWords (σ : Equiv.Perm (Fin 4)) :=
  {w : Fin 4 → B4Letter // decodeWord w ∈ CandB1 4 41 ∧ ∀ i, w (σ i) = w i}
#print axioms Paper7MomentCanonicalNumeric.B4FixedWords

theorem b4_candidate_word_reindex_iff (τ : Equiv.Perm (Fin 4))
    (w : Fin 4 → B4Letter) :
    decodeWord (w ∘ τ) ∈ CandB1 4 41 ↔ decodeWord w ∈ CandB1 4 41 := by
  change (Budget 4 41 (reindex τ (decodeWord w)) ∧
      MomentPass false true false 4 41 (reindex τ (decodeWord w))) ↔
    (Budget 4 41 (decodeWord w) ∧ MomentPass false true false 4 41 (decodeWord w))
  exact and_congr (moment_budget_reindex_iff 4 41 τ τ.bijective (decodeWord w))
    (momentPass_reindex_iff false true false 4 41 τ τ.bijective (decodeWord w))
#print axioms Paper7MomentCanonicalNumeric.b4_candidate_word_reindex_iff

def b4ConjugateWordsEquiv (σ ρ τ : Equiv.Perm (Fin 4))
    (h : ∀ i, τ (σ i) = ρ (τ i)) : B4FixedWords ρ ≃ B4FixedWords σ where
  toFun w := ⟨w.val ∘ τ,
    (b4_candidate_word_reindex_iff τ w.val).mpr w.property.1, by
      intro i
      change w.val (τ (σ i)) = w.val (τ i)
      rw [h i]
      exact w.property.2 (τ i)⟩
  invFun w := ⟨w.val ∘ τ.symm,
    (b4_candidate_word_reindex_iff τ.symm w.val).mpr w.property.1, by
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
#print axioms Paper7MomentCanonicalNumeric.b4ConjugateWordsEquiv

theorem b4_fixed_count_eq_word_count (σ : B4Dihedral) :
    b4FixedCount σ = Fintype.card (B4FixedWords σ.val) :=
  Fintype.card_congr (candB1FixedWordEquiv 4 41 (by decide) σ)
#print axioms Paper7MomentCanonicalNumeric.b4_fixed_count_eq_word_count

theorem b4_fixed_count_conjugate (σ ρ : B4Dihedral) (τ : Equiv.Perm (Fin 4))
    (h : ∀ i, τ (σ.val i) = ρ.val (τ i)) : b4FixedCount σ = b4FixedCount ρ := by
  rw [b4_fixed_count_eq_word_count, b4_fixed_count_eq_word_count]
  exact (Fintype.card_congr (b4ConjugateWordsEquiv σ.val ρ.val τ h)).symm
#print axioms Paper7MomentCanonicalNumeric.b4_fixed_count_conjugate

abbrev b4Rotation (c : Fin 4) : B4Dihedral := dihedralCardRotation 1 (by decide) c
#print axioms Paper7MomentCanonicalNumeric.b4Rotation

abbrev b4Reflection (c : Fin 4) : B4Dihedral := dihedralCardReflection 1 (by decide) c
#print axioms Paper7MomentCanonicalNumeric.b4Reflection

theorem b4_rotation_zero : b4Rotation 0 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  change i + 0 = i
  exact add_zero i
#print axioms Paper7MomentCanonicalNumeric.b4_rotation_zero

theorem b4_rotation_three_count : b4FixedCount (b4Rotation 3) =
    b4FixedCount (b4Rotation 1) := by
  apply b4_fixed_count_conjugate _ _ (b4Reflection 0).val
  intro i
  fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalNumeric.b4_rotation_three_count

theorem b4_reflection_one_count : b4FixedCount (b4Reflection 1) =
    b4FixedCount (b4Rotation 2) := by
  apply b4_fixed_count_conjugate _ _ (Equiv.swap (1 : Fin 4) 2)
  intro i
  fin_cases i <;> decide
#print axioms Paper7MomentCanonicalNumeric.b4_reflection_one_count

theorem b4_reflection_three_count : b4FixedCount (b4Reflection 3) =
    b4FixedCount (b4Rotation 2) := by
  apply b4_fixed_count_conjugate _ _ (Equiv.swap (2 : Fin 4) 3)
  intro i
  fin_cases i <;> decide
#print axioms Paper7MomentCanonicalNumeric.b4_reflection_three_count

theorem b4_reflection_two_count : b4FixedCount (b4Reflection 2) =
    b4FixedCount (b4Reflection 0) := by
  apply b4_fixed_count_conjugate _ _ (b4Reflection 1).val
  intro i
  fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalNumeric.b4_reflection_two_count

theorem b4_affine_fixed_sum :
    (∑ σ : B4Dihedral, b4FixedCount σ) =
      (∑ c : Fin 4, b4FixedCount (b4Rotation c)) +
      (∑ c : Fin 4, b4FixedCount (b4Reflection c)) := by
  calc
    (∑ σ : B4Dihedral, b4FixedCount σ) =
        ∑ c : Fin 4 ⊕ Fin 4, b4FixedCount (dihedralCardEncode 1 (by decide) c) :=
      ((dihedralCardAffineEquiv 1 (by decide)).sum_comp b4FixedCount).symm
    _ = _ := Fintype.sum_sum_type _
#print axioms Paper7MomentCanonicalNumeric.b4_affine_fixed_sum

theorem b4_nonidentity_grouped :
    b4NonidentityFixedSum = 2 * b4FixedCount (b4Rotation 1) +
      3 * b4FixedCount (b4Rotation 2) + 2 * b4FixedCount (b4Reflection 0) := by
  have h := b4_affine_fixed_sum
  rw [Fin.sum_univ_four, Fin.sum_univ_four, b4_rotation_zero,
    b4_rotation_three_count, b4_reflection_one_count,
    b4_reflection_two_count, b4_reflection_three_count] at h
  have he := Finset.sum_erase_add (Finset.univ : Finset B4Dihedral)
    b4FixedCount (Finset.mem_univ (1 : B4Dihedral))
  change b4NonidentityFixedSum + b4FixedCount 1 =
    (∑ σ : B4Dihedral, b4FixedCount σ) at he
  omega
#print axioms Paper7MomentCanonicalNumeric.b4_nonidentity_grouped

end Paper7MomentCanonicalNumeric
