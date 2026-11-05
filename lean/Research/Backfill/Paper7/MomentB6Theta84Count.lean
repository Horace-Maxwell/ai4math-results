import Research.Backfill.Paper7.MomentB6Theta84Rows
import Research.Backfill.Paper7.MomentB6NineCount

/-! Pending original theta84 fibre count. The complete original PQ guard iff
is imported from the still-pending Rows source. All row identities below
are pointwise, and the three families are separated by their actual qSum.
No numerical total or statistical injectivity is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

theorem b6Theta84_row_qSums :
    (∀ i : Fin 6, qSum (b6Theta84SingleRow i) = 1) ∧
    (∀ t : B6NinePair, qSum (b6Theta84FullQRow t.val.1 t.val.2) = 7) ∧
    (∀ t : B6NinePair, qSum (b6Theta84ZeroQRow t.val.1 t.val.2) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp [qSum, b6Theta84SingleRow]
  · intro t
    exact b6SevenDouble_sum t.val.1 t.val.2 t.property
  · intro t
    simp [qSum, b6Theta84ZeroQRow]
#print axioms Paper7MomentCounts.b6Theta84_row_qSums

theorem b6Theta84SingleRow_injective : Function.Injective b6Theta84SingleRow := by
  intro i j h
  by_contra hij
  have he := congrArg (fun x : PQ 6 => x.1 i) h
  simp [b6Theta84SingleRow, hij] at he
#print axioms Paper7MomentCounts.b6Theta84SingleRow_injective

theorem b6Theta84FullQRow_injective :
    Function.Injective (fun t : B6NinePair => b6Theta84FullQRow t.val.1 t.val.2) := by
  intro a b h
  have hi : a.val.1 = b.val.1 := by
    by_contra hn
    have he := congrArg (fun x : PQ 6 => x.2 a.val.1) h
    by_cases hab : a.val.1 = b.val.2 <;>
      simp [b6Theta84FullQRow, b6SevenDouble, hn, hab] at he
    exact b.property he.symm
  have hj : a.val.2 = b.val.2 := by
    by_contra hn
    have he := congrArg (fun x : PQ 6 => x.2 a.val.2) h
    have ha : a.val.2 ≠ a.val.1 := Ne.symm a.property
    have hb : a.val.2 ≠ b.val.1 := by simpa only [← hi] using ha
    simp [b6Theta84FullQRow, b6SevenDouble, ha, hb, hn] at he
  exact Subtype.ext (Prod.ext hi hj)
#print axioms Paper7MomentCounts.b6Theta84FullQRow_injective

theorem b6Theta84ZeroQRow_injective :
    Function.Injective (fun t : B6NinePair => b6Theta84ZeroQRow t.val.1 t.val.2) := by
  intro a b h
  apply b6_nine_pair_data_injective.1
  change (b6TwoPoint 6 3 a.val.1 a.val.2, (0 : ℕ)) =
    (b6TwoPoint 6 3 b.val.1 b.val.2, (0 : ℕ))
  apply Prod.ext
  · exact congrArg (fun x : PQ 6 => x.1) h
  · rfl
#print axioms Paper7MomentCounts.b6Theta84ZeroQRow_injective

def b6Theta84TemplateRow : Fin 6 ⊕ (B6NinePair ⊕ B6NinePair) → PQ 6 :=
  Sum.elim b6Theta84SingleRow
    (Sum.elim (fun t => b6Theta84FullQRow t.val.1 t.val.2)
      (fun t => b6Theta84ZeroQRow t.val.1 t.val.2))
#print axioms Paper7MomentCounts.b6Theta84TemplateRow

theorem b6Theta84TemplateRow_injective : Function.Injective b6Theta84TemplateRow := by
  unfold b6Theta84TemplateRow
  apply b6Theta84SingleRow_injective.sumElim
  · apply b6Theta84FullQRow_injective.sumElim b6Theta84ZeroQRow_injective
    intro a b he
    have hq := congrArg qSum he
    rw [b6Theta84_row_qSums.2.1, b6Theta84_row_qSums.2.2] at hq
    omega
  · intro a b
    rcases b with b | b <;> intro he <;> have hq := congrArg qSum he
    · change qSum (b6Theta84SingleRow a) = qSum (b6Theta84FullQRow b.val.1 b.val.2) at hq
      rw [b6Theta84_row_qSums.1, b6Theta84_row_qSums.2.1] at hq
      omega
    · change qSum (b6Theta84SingleRow a) = qSum (b6Theta84ZeroQRow b.val.1 b.val.2) at hq
      rw [b6Theta84_row_qSums.1, b6Theta84_row_qSums.2.2] at hq
      omega
#print axioms Paper7MomentCounts.b6Theta84TemplateRow_injective

theorem b6Theta84TemplateRow_accept (t : Fin 6 ⊕ (B6NinePair ⊕ B6NinePair)) :
    b6CandidateGuard (b6Theta84TemplateRow t) ∧ theta (b6Theta84TemplateRow t) = 84 := by
  rcases t with t | t | t
  · exact b6Theta84SingleRow_accept t
  · exact b6Theta84FullQRow_accept t.val.1 t.val.2 t.property
  · exact b6Theta84ZeroQRow_accept t.val.1 t.val.2 t.property
#print axioms Paper7MomentCounts.b6Theta84TemplateRow_accept

def b6Theta84GuardEquiv :
    (Fin 6 ⊕ (B6NinePair ⊕ B6NinePair)) ≃
      {x : PQ 6 // b6CandidateGuard x ∧ theta x = 84} :=
  Equiv.ofBijective
    (fun t => ⟨b6Theta84TemplateRow t, b6Theta84TemplateRow_accept t⟩)
    ⟨fun _ _ h => b6Theta84TemplateRow_injective (congrArg Subtype.val h), by
      intro x
      rcases (b6_theta84_guard_iff x.val).mp x.property with
        ⟨i, hi⟩ | ⟨i, j, hij, he⟩ | ⟨i, j, hij, he⟩
      · exact ⟨Sum.inl i, Subtype.ext hi.symm⟩
      · exact ⟨Sum.inr (Sum.inl ⟨(i,j),hij⟩), Subtype.ext he.symm⟩
      · exact ⟨Sum.inr (Sum.inr ⟨(i,j),hij⟩), Subtype.ext he.symm⟩⟩
#print axioms Paper7MomentCounts.b6Theta84GuardEquiv

def b6Theta84B1Equiv :
    (Fin 6 ⊕ (B6NinePair ⊕ B6NinePair)) ≃
      {x : PQ 6 // x ∈ CandB1 6 42 ∧ theta x = 84} :=
  b6Theta84GuardEquiv.trans (Equiv.subtypeEquivRight
    (fun x => and_congr (b6_candB1_iff_guard x).symm Iff.rfl))
#print axioms Paper7MomentCounts.b6Theta84B1Equiv

def b6Theta84D2Equiv :
    (Fin 6 ⊕ (B6NinePair ⊕ B6NinePair)) ≃
      {x : PQ 6 // x ∈ CandD2 6 42 ∧ theta x = 84} :=
  b6Theta84GuardEquiv.trans (Equiv.subtypeEquivRight
    (fun x => and_congr (b6_candD2_iff_guard x).symm Iff.rfl))
#print axioms Paper7MomentCounts.b6Theta84D2Equiv

theorem b6_theta84_candB1_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 84}.ncard = 66 := by
  change Nat.card {x : PQ 6 // x ∈ CandB1 6 42 ∧ theta x = 84} = 66
  rw [Nat.card_congr b6Theta84B1Equiv.symm]
  simp [Nat.card_eq_fintype_card, b6_nine_family_cards.1]
#print axioms Paper7MomentCounts.b6_theta84_candB1_ncard

theorem b6_theta84_candD2_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 84}.ncard = 66 := by
  change Nat.card {x : PQ 6 // x ∈ CandD2 6 42 ∧ theta x = 84} = 66
  rw [Nat.card_congr b6Theta84D2Equiv.symm]
  simp [Nat.card_eq_fintype_card, b6_nine_family_cards.1]
#print axioms Paper7MomentCounts.b6_theta84_candD2_ncard

end Paper7MomentCounts
