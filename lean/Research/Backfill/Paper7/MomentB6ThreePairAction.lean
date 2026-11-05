import Research.Backfill.Paper7.MomentB6ThreePairComplete
import Research.Backfill.Paper7.MomentB6DihedralGrouping

/-! Transport of the original repeated-three-position fibre to actual D6.
All statements are proposed and uncompiled. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalSix
open BackfillPaper7.Challenge.Legacy Paper7MomentCounts
open scoped BigOperators Classical

theorem b6_rotation_three_word_iff (w : Fin 6 → B6Letter) :
    (∀ i,w ((b6Rotation 3).val i) = w i) ↔ w = ![w 0,w 1,w 2,w 0,w 1,w 2] := by
  constructor
  · intro h
    have h03 : w 3 = w 0 := h 0
    have h14 : w 4 = w 1 := h 1
    have h25 : w 5 = w 2 := h 2
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact h03
    · exact h14
    · exact h25
  · intro h i
    rw [h]
    fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalSix.b6_rotation_three_word_iff

theorem b6_rotation_three_decode_iff (w : Fin 6 → B6Letter) :
    (∀ i,w ((b6Rotation 3).val i) = w i) ↔
      ∃ x : PQ 3,decodeWord w = b6ThreePairRow x := by
  constructor
  · intro h
    have hw := (b6_rotation_three_word_iff w).mp h
    refine ⟨(![(w 0).1.val,(w 1).1.val,(w 2).1.val],
      ![(w 0).2.val,(w 1).2.val,(w 2).2.val]),?_⟩
    rw [hw]
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  · rintro ⟨x,hx⟩
    have hp (i : Fin 6) := congrArg (fun z : PQ 6 => z.1 i) hx
    have hq (i : Fin 6) := congrArg (fun z : PQ 6 => z.2 i) hx
    apply (b6_rotation_three_word_iff w).mpr
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · apply Prod.ext
      · apply Fin.ext
        exact (hp 3).trans (hp 0).symm
      · apply Fin.ext
        exact (hq 3).trans (hq 0).symm
    · apply Prod.ext
      · apply Fin.ext
        exact (hp 4).trans (hp 1).symm
      · apply Fin.ext
        exact (hq 4).trans (hq 1).symm
    · apply Prod.ext
      · apply Fin.ext
        exact (hp 5).trans (hp 2).symm
      · apply Fin.ext
        exact (hq 5).trans (hq 2).symm
#print axioms Paper7MomentCanonicalSix.b6_rotation_three_decode_iff

def b6RotationThreePQEquiv : B6FixedWords (b6Rotation 3).val ≃
    {x : PQ 6 // x ∈ CandB1 6 42 ∧ ∃ y : PQ 3,x = b6ThreePairRow y} :=
  (Equiv.subtypeEquivRight (fun w =>
    and_congr Iff.rfl (b6_rotation_three_decode_iff w))).trans
    (predicateWordEquiv 6 42 (fun x => x ∈ CandB1 6 42 ∧
      ∃ y : PQ 3,x = b6ThreePairRow y) (fun _ hx => hx.1.1)).symm
#print axioms Paper7MomentCanonicalSix.b6RotationThreePQEquiv

theorem b6_rotation_three_fixed_count : b6FixedCount (b6Rotation 3) = 129 := by
  rw [b6_fixed_count_eq_word_count]
  calc
    Fintype.card (B6FixedWords (b6Rotation 3).val) =
        Nat.card (B6FixedWords (b6Rotation 3).val) := Nat.card_eq_fintype_card.symm
    _ = Nat.card {x : PQ 6 // x ∈ CandB1 6 42 ∧ ∃ y : PQ 3,x = b6ThreePairRow y} :=
      Nat.card_congr b6RotationThreePQEquiv
    _ = 129 := b6_three_pair_candB1_ncard
#print axioms Paper7MomentCanonicalSix.b6_rotation_three_fixed_count

theorem b6_odd_reflection_fixed_counts :
    b6FixedCount (b6Reflection 1) = 129 ∧ b6FixedCount (b6Reflection 3) = 129 ∧
      b6FixedCount (b6Reflection 5) = 129 := by
  exact ⟨b6_reflection_one_count.trans b6_rotation_three_fixed_count,
    b6_reflection_three_count.trans (b6_reflection_one_count.trans b6_rotation_three_fixed_count),
    b6_reflection_five_count.trans (b6_reflection_one_count.trans b6_rotation_three_fixed_count)⟩
#print axioms Paper7MomentCanonicalSix.b6_odd_reflection_fixed_counts

end Paper7MomentCanonicalSix
