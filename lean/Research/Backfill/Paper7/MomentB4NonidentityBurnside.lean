import Research.Backfill.Paper7.MomentFixedBlockCounts
import Research.Backfill.Paper7.MomentB4GapNumericComplete

/-! Complete reduction of the two original b = 4 canonical counts to
the seven nonidentity fixed-point sets. These are uncompiled source candidates.
No concrete nonidentity fixed-point total or table completeness is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge.Legacy
open Paper7MomentCounts
open scoped BigOperators Classical

abbrev B4Dihedral := dihedralSubgroup 4 (by decide)
#print axioms Paper7MomentCanonicalNumeric.B4Dihedral

def b4FixedCount (σ : B4Dihedral) : ℕ :=
  Fintype.card (CandB1FixedBy 4 41 (by decide) σ)
#print axioms Paper7MomentCanonicalNumeric.b4FixedCount

def b4NonidentityFixedSum : ℕ :=
  ∑ σ ∈ (Finset.univ : Finset B4Dihedral).erase 1, b4FixedCount σ
#print axioms Paper7MomentCanonicalNumeric.b4NonidentityFixedSum

def b4IdentityFixedEquiv :
    CandB1FixedBy 4 41 (by decide) (1 : B4Dihedral) ≃ ↥(CandB1 4 41) := by
  letI : MulAction B4Dihedral ↥(CandB1 4 41) :=
    candB1DihedralAction 4 41 (by decide)
  exact
    { toFun := fun x => x.val
      invFun := fun x => ⟨x, by
        change (1 : B4Dihedral) • x = x
        exact one_smul B4Dihedral x⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun _ => rfl }
#print axioms Paper7MomentCanonicalNumeric.b4IdentityFixedEquiv

theorem b4_identity_fixed_count : b4FixedCount 1 = 410544 := by
  calc
    b4FixedCount 1 = Fintype.card ↥(CandB1 4 41) :=
      Fintype.card_congr b4IdentityFixedEquiv
    _ = (CandB1 4 41).ncard := Set.fintypeCard_eq_ncard _
    _ = 410544 := Paper7MomentGapNumeric.candB1_4_41_count
#print axioms Paper7MomentCanonicalNumeric.b4_identity_fixed_count

theorem b4_nonidentity_parameter_count :
    ((Finset.univ : Finset B4Dihedral).erase 1).card = 7 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  change Fintype.card (dihedralSubgroup 4 (by decide)) - 1 = 7
  rw [dihedralSubgroup_card]
#print axioms Paper7MomentCanonicalNumeric.b4_nonidentity_parameter_count

theorem b4_burnside_without_identity :
    (canonB1 4 41).ncard * 8 = 410544 + b4NonidentityFixedSum := by
  have hb := candB1_burnside_two_b 4 41 (by decide) (by decide)
  change (∑ σ : B4Dihedral, b4FixedCount σ) = (canonB1 4 41).ncard * 8 at hb
  have he := Finset.sum_erase_add (Finset.univ : Finset B4Dihedral)
    b4FixedCount (Finset.mem_univ (1 : B4Dihedral))
  change b4NonidentityFixedSum + b4FixedCount 1 =
    (∑ σ : B4Dihedral, b4FixedCount σ) at he
  rw [b4_identity_fixed_count] at he
  calc
    (canonB1 4 41).ncard * 8 = ∑ σ : B4Dihedral, b4FixedCount σ := hb.symm
    _ = b4NonidentityFixedSum + 410544 := he.symm
    _ = 410544 + b4NonidentityFixedSum := Nat.add_comm _ _
#print axioms Paper7MomentCanonicalNumeric.b4_burnside_without_identity

def b4NonidentityBlockWordSum : ℕ :=
  ∑ σ ∈ (Finset.univ : Finset B4Dihedral).erase 1,
    Fintype.card (CandB1BlockWords 4 41 (by decide) σ)
#print axioms Paper7MomentCanonicalNumeric.b4NonidentityBlockWordSum

theorem b4_nonidentity_fixed_eq_block_words :
    b4NonidentityFixedSum = b4NonidentityBlockWordSum := by
  unfold b4NonidentityFixedSum b4NonidentityBlockWordSum
  apply Finset.sum_congr rfl
  intro σ _
  exact candB1_fixedBy_card_eq_blockWords_card 4 41 (by decide) σ
#print axioms Paper7MomentCanonicalNumeric.b4_nonidentity_fixed_eq_block_words

theorem canonB1_b4_count_iff_nonidentity :
    (canonB1 4 41).ncard = 52641 ↔ b4NonidentityFixedSum = 10584 := by
  have h := b4_burnside_without_identity
  omega
#print axioms Paper7MomentCanonicalNumeric.canonB1_b4_count_iff_nonidentity

theorem canonD2_b4_count_iff_nonidentity :
    (canonD2 4 41).ncard = 52641 ↔ b4NonidentityFixedSum = 10584 := by
  rw [← canonB1_ncard_eq_canonD2 4 41 (by decide) (by decide) ⟨2, rfl⟩]
  exact canonB1_b4_count_iff_nonidentity
#print axioms Paper7MomentCanonicalNumeric.canonD2_b4_count_iff_nonidentity

theorem b4_both_original_canonical_clauses_iff :
    ((canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641) ∧
      ((canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641) ↔
        b4NonidentityBlockWordSum = 10584 := by
  rw [← b4_nonidentity_fixed_eq_block_words]
  constructor
  · intro h
    exact canonB1_b4_count_iff_nonidentity.mp h.1.2
  · intro h
    exact ⟨⟨canonB1_finite 4 41, canonB1_b4_count_iff_nonidentity.mpr h⟩,
      ⟨canonD2_finite 4 41, canonD2_b4_count_iff_nonidentity.mpr h⟩⟩
#print axioms Paper7MomentCanonicalNumeric.b4_both_original_canonical_clauses_iff

end Paper7MomentCanonicalNumeric
