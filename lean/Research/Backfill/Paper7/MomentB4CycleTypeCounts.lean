import Research.Backfill.Paper7.MomentB4CycleConjugacy

/-! Source-only: the original accepted predicate is preserved on every
constant, two-block and three-block word. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge.Legacy Paper7MomentCounts
open scoped BigOperators Classical

theorem b4_rotation_one_word_iff (w : Fin 4 → B4Letter) :
    (∀ i, w ((b4Rotation 1).val i) = w i) ↔ w = fun _ => w 0 := by
  constructor
  · intro h
    have h01 : w 1 = w 0 := h 0
    have h12 : w 2 = w 1 := h 1
    have h23 : w 3 = w 2 := h 2
    funext i
    fin_cases i
    · rfl
    · exact h01
    · exact h12.trans h01
    · exact h23.trans (h12.trans h01)
  · intro h i
    rw [h]
#print axioms Paper7MomentCanonicalNumeric.b4_rotation_one_word_iff

theorem b4_rotation_two_word_iff (w : Fin 4 → B4Letter) :
    (∀ i, w ((b4Rotation 2).val i) = w i) ↔ w = ![w 0, w 1, w 0, w 1] := by
  constructor
  · intro h
    have h02 : w 2 = w 0 := h 0
    have h13 : w 3 = w 1 := h 1
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact h02
    · exact h13
  · intro h i
    rw [h]
    fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalNumeric.b4_rotation_two_word_iff

theorem b4_reflection_zero_word_iff (w : Fin 4 → B4Letter) :
    (∀ i, w ((b4Reflection 0).val i) = w i) ↔ w = ![w 0, w 1, w 2, w 1] := by
  constructor
  · intro h
    have h13 : w 3 = w 1 := h 1
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact h13
  · intro h i
    rw [h]
    fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalNumeric.b4_reflection_zero_word_iff

abbrev B4Type4 := {a : B4Letter // decodeWord (fun _ : Fin 4 => a) ∈ CandB1 4 41}
#print axioms Paper7MomentCanonicalNumeric.B4Type4

abbrev B4Type22 := {a : B4Letter × B4Letter //
  decodeWord (![a.1, a.2, a.1, a.2] : Fin 4 → B4Letter) ∈ CandB1 4 41}
#print axioms Paper7MomentCanonicalNumeric.B4Type22

abbrev B4Type112 := {a : B4Letter × B4Letter × B4Letter //
  decodeWord (![a.1, a.2.1, a.2.2, a.2.1] : Fin 4 → B4Letter) ∈ CandB1 4 41}
#print axioms Paper7MomentCanonicalNumeric.B4Type112

def b4Type4Equiv : B4FixedWords (b4Rotation 1).val ≃ B4Type4 where
  toFun w := ⟨w.val 0, by
    rw [← (b4_rotation_one_word_iff w.val).mp w.property.2]
    exact w.property.1⟩
  invFun a := ⟨fun _ => a.val, a.property, fun _ => rfl⟩
  left_inv w := by
    apply Subtype.ext
    exact ((b4_rotation_one_word_iff w.val).mp w.property.2).symm
  right_inv a := by apply Subtype.ext; rfl
#print axioms Paper7MomentCanonicalNumeric.b4Type4Equiv

def b4Type22Equiv : B4FixedWords (b4Rotation 2).val ≃ B4Type22 where
  toFun w := ⟨(w.val 0, w.val 1), by
    rw [← (b4_rotation_two_word_iff w.val).mp w.property.2]
    exact w.property.1⟩
  invFun a := ⟨![a.val.1, a.val.2, a.val.1, a.val.2], a.property, by
    intro i
    fin_cases i <;> rfl⟩
  left_inv w := by
    apply Subtype.ext
    exact ((b4_rotation_two_word_iff w.val).mp w.property.2).symm
  right_inv a := by apply Subtype.ext; rfl
#print axioms Paper7MomentCanonicalNumeric.b4Type22Equiv

def b4Type112Equiv : B4FixedWords (b4Reflection 0).val ≃ B4Type112 where
  toFun w := ⟨(w.val 0, w.val 1, w.val 2), by
    rw [← (b4_reflection_zero_word_iff w.val).mp w.property.2]
    exact w.property.1⟩
  invFun a := ⟨![a.val.1, a.val.2.1, a.val.2.2, a.val.2.1], a.property, by
    intro i
    fin_cases i <;> rfl⟩
  left_inv w := by
    apply Subtype.ext
    exact ((b4_reflection_zero_word_iff w.val).mp w.property.2).symm
  right_inv a := by apply Subtype.ext; rfl
#print axioms Paper7MomentCanonicalNumeric.b4Type112Equiv

theorem b4_nonidentity_cycle_type_sum :
    b4NonidentityFixedSum = 2 * Fintype.card B4Type4 +
      3 * Fintype.card B4Type22 + 2 * Fintype.card B4Type112 := by
  rw [b4_nonidentity_grouped, b4_fixed_count_eq_word_count,
    b4_fixed_count_eq_word_count, b4_fixed_count_eq_word_count,
    Fintype.card_congr b4Type4Equiv, Fintype.card_congr b4Type22Equiv,
    Fintype.card_congr b4Type112Equiv]
#print axioms Paper7MomentCanonicalNumeric.b4_nonidentity_cycle_type_sum

theorem b4_canonical_clauses_iff_cycle_types :
    ((canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641) ∧
      ((canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641) ↔
        2 * Fintype.card B4Type4 + 3 * Fintype.card B4Type22 +
          2 * Fintype.card B4Type112 = 10584 := by
  rw [b4_both_original_canonical_clauses_iff,
    ← b4_nonidentity_fixed_eq_block_words, b4_nonidentity_cycle_type_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_canonical_clauses_iff_cycle_types

end Paper7MomentCanonicalNumeric
