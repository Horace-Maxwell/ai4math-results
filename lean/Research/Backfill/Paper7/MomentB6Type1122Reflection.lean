import Research.Backfill.Paper7.MomentB6Type1122OriginalFibre
import Research.Backfill.Paper7.MomentB6DihedralGrouping

/-! UNCOMPILED source-only transport to the actual frozen reflection 0.
This endpoint is an exact cardinal of full original candidates, not a
numerical fixed-count claim. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalSix
open BackfillPaper7.Challenge.Legacy Paper7MomentCounts
open scoped BigOperators Classical

theorem b6_reflection_zero_word_iff (w : Fin 6 → B6Letter) :
    (∀ i, w ((b6Reflection 0).val i) = w i) ↔
      w = ![w 0,w 1,w 2,w 3,w 2,w 1] := by
  constructor
  · intro h
    have h15 : w 5 = w 1 := h 1
    have h24 : w 4 = w 2 := h 2
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · exact h24
    · exact h15
  · intro h i
    rw [h]
    fin_cases i <;> rfl
#print axioms Paper7MomentCanonicalSix.b6_reflection_zero_word_iff

theorem b6_reflection_zero_decode_iff (w : Fin 6 → B6Letter) :
    (∀ i, w ((b6Reflection 0).val i) = w i) ↔
      ∃ x : PQ 4, decodeWord w = b6Type1122Row x := by
  constructor
  · intro h
    have hw := (b6_reflection_zero_word_iff w).mp h
    refine ⟨(![(w 0).1.val,(w 1).1.val,(w 2).1.val,(w 3).1.val],
      ![(w 0).2.val,(w 1).2.val,(w 2).2.val,(w 3).2.val]),?_⟩
    rw [hw]
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  · rintro ⟨x,he⟩
    have hp (i : Fin 6) : (w i).1.val =
        (![x.1 0,x.1 1,x.1 2,x.1 3,x.1 2,x.1 1] : Fin 6 → ℕ) i :=
      congrArg (fun v : PQ 6 => v.1 i) he
    have hq (i : Fin 6) : (w i).2.val =
        (![x.2 0,x.2 1,x.2 2,x.2 3,x.2 2,x.2 1] : Fin 6 → ℕ) i :=
      congrArg (fun v : PQ 6 => v.2 i) he
    apply (b6_reflection_zero_word_iff w).mpr
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · apply Prod.ext
      · apply Fin.ext
        exact (hp 4).trans (hp 2).symm
      · apply Fin.ext
        exact (hq 4).trans (hq 2).symm
    · apply Prod.ext
      · apply Fin.ext
        exact (hp 5).trans (hp 1).symm
      · apply Fin.ext
        exact (hq 5).trans (hq 1).symm
#print axioms Paper7MomentCanonicalSix.b6_reflection_zero_decode_iff

def b6ReflectionZeroPQEquiv : B6FixedWords (b6Reflection 0).val ≃
    {x : PQ 6 // x ∈ CandB1 6 42 ∧ ∃ u : PQ 4, x = b6Type1122Row u} :=
  (Equiv.subtypeEquivRight (fun w =>
    and_congr Iff.rfl (b6_reflection_zero_decode_iff w))).trans
    (predicateWordEquiv 6 42 (fun x => x ∈ CandB1 6 42 ∧
      ∃ u : PQ 4, x = b6Type1122Row u) (fun _ hx => hx.1.1)).symm
#print axioms Paper7MomentCanonicalSix.b6ReflectionZeroPQEquiv

def b6Type1122ParameterRowsEquiv :
    {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} ≃
      {x : PQ 6 // x ∈ CandB1 6 42 ∧ ∃ u : PQ 4, x = b6Type1122Row u} :=
  Equiv.ofBijective
    (fun u => ⟨b6Type1122Row u.val,u.property,u.val,rfl⟩)
    (by
      constructor
      · intro u v h
        apply Subtype.ext
        exact b6_type1122_row_injective (congrArg Subtype.val h)
      · rintro ⟨x,hx,u,hu⟩
        refine ⟨⟨u,?_⟩,?_⟩
        · rw [← hu]
          exact hx
        · exact Subtype.ext hu.symm)
#print axioms Paper7MomentCanonicalSix.b6Type1122ParameterRowsEquiv

theorem b6_reflection_zero_count_eq_original_type1122 :
    b6FixedCount (b6Reflection 0) =
      Nat.card {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} := by
  rw [b6_fixed_count_eq_word_count]
  calc
    Fintype.card (B6FixedWords (b6Reflection 0).val) =
        Nat.card (B6FixedWords (b6Reflection 0).val) := Nat.card_eq_fintype_card.symm
    _ = Nat.card {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} :=
      Nat.card_congr (b6ReflectionZeroPQEquiv.trans b6Type1122ParameterRowsEquiv.symm)
#print axioms Paper7MomentCanonicalSix.b6_reflection_zero_count_eq_original_type1122

theorem b6_reflection_zero_count_eq_original_type1122_D2 :
    b6FixedCount (b6Reflection 0) =
      Nat.card {u : PQ 4 // b6Type1122Row u ∈ CandD2 6 42} := by
  rw [candD2_eq_candB1_of_even 6 42 (by decide)]
  exact b6_reflection_zero_count_eq_original_type1122
#print axioms Paper7MomentCanonicalSix.b6_reflection_zero_count_eq_original_type1122_D2

end Paper7MomentCanonicalSix
