import Research.Backfill.Paper7.MomentB6DihedralGrouping
import Research.Backfill.Paper7.MomentB6ConstantRows
import Research.Backfill.Paper7.MomentB6ThreeThreeRows

/-! Source-only transport from the full original constant and alternating
PQ fibres to the actual frozen D6 action. All three imported new sources
remain pending until Root supplies actual successful producers. This file
adds no numerical hypothesis and retains both original candidate identities. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalSix
open BackfillPaper7.Challenge.Legacy Paper7MomentCounts
open scoped BigOperators Classical

theorem b6_rotation_one_word_iff (w : Fin 6 → B6Letter) :
    (∀ i, w ((b6Rotation 1).val i) = w i) ↔ w = fun _ => w 0 := by
  constructor
  · intro h
    have h01 : w 1 = w 0 := h 0
    have h12 : w 2 = w 1 := h 1
    have h23 : w 3 = w 2 := h 2
    have h34 : w 4 = w 3 := h 3
    have h45 : w 5 = w 4 := h 4
    funext i
    fin_cases i
    · rfl
    · exact h01
    · exact h12.trans h01
    · exact h23.trans (h12.trans h01)
    · exact h34.trans (h23.trans (h12.trans h01))
    · exact h45.trans (h34.trans (h23.trans (h12.trans h01)))
  · intro h i
    rw [h]
#print axioms Paper7MomentCanonicalSix.b6_rotation_one_word_iff

theorem b6_rotation_two_word_iff (w : Fin 6 → B6Letter) :
    (∀ i, w ((b6Rotation 2).val i) = w i) ↔ w = ![w 0,w 1,w 0,w 1,w 0,w 1] := by
  constructor
  · intro h
    have h02 : w 2 = w 0 := h 0
    have h24 : w 4 = w 2 := h 2
    have h13 : w 3 = w 1 := h 1
    have h35 : w 5 = w 3 := h 3
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact h02
    · exact h13
    · exact h24.trans h02
    · exact h35.trans h13
  · intro h i
    rw [h]
    fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalSix.b6_rotation_two_word_iff

theorem b6_rotation_one_fixed_count : b6FixedCount (b6Rotation 1) = 0 := by
  rw [b6_fixed_count_eq_word_count]
  let : IsEmpty (B6FixedWords (b6Rotation 1).val) := ⟨fun w => by
    have he := (b6_rotation_one_word_iff w.val).mp w.property.2
    have hx := w.property.1
    rw [he] at hx
    exact b6_constant_candB1_impossible (w.val 0).1.val (w.val 0).2.val hx⟩
  exact Fintype.card_of_isEmpty
#print axioms Paper7MomentCanonicalSix.b6_rotation_one_fixed_count

theorem b6_rotation_five_fixed_count : b6FixedCount (b6Rotation 5) = 0 :=
  b6_rotation_five_count.trans b6_rotation_one_fixed_count
#print axioms Paper7MomentCanonicalSix.b6_rotation_five_fixed_count

theorem b6_rotation_two_decode_iff (w : Fin 6 → B6Letter) :
    (∀ i, w ((b6Rotation 2).val i) = w i) ↔
      ∃ p r q s : ℕ, decodeWord w = b6ThreeThreeRow p r q s := by
  constructor
  · intro h
    have hw := (b6_rotation_two_word_iff w).mp h
    refine ⟨(w 0).1.val,(w 1).1.val,(w 0).2.val,(w 1).2.val,?_⟩
    rw [hw]
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  · rintro ⟨p,r,q,s,he⟩
    have hp (i : Fin 6) : (w i).1.val = (![p,r,p,r,p,r] : Fin 6 → ℕ) i :=
      congrArg (fun x : PQ 6 => x.1 i) he
    have hq (i : Fin 6) : (w i).2.val = (![q,s,q,s,q,s] : Fin 6 → ℕ) i :=
      congrArg (fun x : PQ 6 => x.2 i) he
    apply (b6_rotation_two_word_iff w).mpr
    funext i
    fin_cases i
    · rfl
    · rfl
    · apply Prod.ext
      · apply Fin.ext
        exact (hp 2).trans (hp 0).symm
      · apply Fin.ext
        exact (hq 2).trans (hq 0).symm
    · apply Prod.ext
      · apply Fin.ext
        exact (hp 3).trans (hp 1).symm
      · apply Fin.ext
        exact (hq 3).trans (hq 1).symm
    · apply Prod.ext
      · apply Fin.ext
        exact (hp 4).trans (hp 0).symm
      · apply Fin.ext
        exact (hq 4).trans (hq 0).symm
    · apply Prod.ext
      · apply Fin.ext
        exact (hp 5).trans (hp 1).symm
      · apply Fin.ext
        exact (hq 5).trans (hq 1).symm
#print axioms Paper7MomentCanonicalSix.b6_rotation_two_decode_iff

def b6RotationTwoPQEquiv : B6FixedWords (b6Rotation 2).val ≃
    {x : PQ 6 // x ∈ CandB1 6 42 ∧
      ∃ p r q s : ℕ, x = b6ThreeThreeRow p r q s} :=
  (Equiv.subtypeEquivRight (fun w =>
    and_congr Iff.rfl (b6_rotation_two_decode_iff w))).trans
    (predicateWordEquiv 6 42 (fun x => x ∈ CandB1 6 42 ∧
      ∃ p r q s : ℕ, x = b6ThreeThreeRow p r q s) (fun _ hx => hx.1.1)).symm
#print axioms Paper7MomentCanonicalSix.b6RotationTwoPQEquiv

theorem b6_rotation_two_fixed_count : b6FixedCount (b6Rotation 2) = 4 := by
  rw [b6_fixed_count_eq_word_count]
  calc
    Fintype.card (B6FixedWords (b6Rotation 2).val) =
        Nat.card (B6FixedWords (b6Rotation 2).val) := Nat.card_eq_fintype_card.symm
    _ = Nat.card {x : PQ 6 // x ∈ CandB1 6 42 ∧
        ∃ p r q s : ℕ, x = b6ThreeThreeRow p r q s} :=
      Nat.card_congr b6RotationTwoPQEquiv
    _ = 4 := b6_three_three_candB1_ncard
#print axioms Paper7MomentCanonicalSix.b6_rotation_two_fixed_count

theorem b6_rotation_four_fixed_count : b6FixedCount (b6Rotation 4) = 4 :=
  b6_rotation_four_count.trans b6_rotation_two_fixed_count
#print axioms Paper7MomentCanonicalSix.b6_rotation_four_fixed_count

theorem b6_nonidentity_two_remaining :
    b6NonidentityFixedSum = 8 + 4 * b6FixedCount (b6Rotation 3) +
      3 * b6FixedCount (b6Reflection 0) := by
  rw [b6_nonidentity_grouped, b6_rotation_one_fixed_count, b6_rotation_two_fixed_count]
#print axioms Paper7MomentCanonicalSix.b6_nonidentity_two_remaining

theorem b6_canonB1_two_remaining_fixed_types :
    (canonB1 6 42).ncard * 12 = (CandB1 6 42).ncard + 8 +
      4 * b6FixedCount (b6Rotation 3) + 3 * b6FixedCount (b6Reflection 0) := by
  rw [b6_burnside_without_identity, b6_nonidentity_two_remaining]
  omega
#print axioms Paper7MomentCanonicalSix.b6_canonB1_two_remaining_fixed_types

theorem b6_canonD2_two_remaining_fixed_types :
    (canonD2 6 42).ncard * 12 = (CandD2 6 42).ncard + 8 +
      4 * b6FixedCount (b6Rotation 3) + 3 * b6FixedCount (b6Reflection 0) := by
  rw [← canonB1_ncard_eq_canonD2 6 42 (by decide) (by decide) ⟨3,rfl⟩,
    candD2_ncard_eq_candB1_of_even 6 42 (by decide)]
  exact b6_canonB1_two_remaining_fixed_types
#print axioms Paper7MomentCanonicalSix.b6_canonD2_two_remaining_fixed_types

end Paper7MomentCanonicalSix
