import Research.Backfill.Paper7.MomentB6Theta252Rows

/-! Proposed complete original theta252 fibre counts. The two templates are
injected pointwise into the original ordered PQ6 guard, then transported
separately to original CandB1 and CandD2. All three sources are uncompiled. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

theorem b6Theta252_row_qSums :
    (∀ i : Fin 6,qSum (b6Theta252SingleRow i) = 1) ∧
      (∀ t : B6NinePair,qSum (b6Theta252FullQRow t.val.1 t.val.2) = 14) := by
  constructor
  · intro i
    simp [qSum,b6Theta252SingleRow]
  · intro t
    simpa only [qSum,b6Theta252FullQRow] using
      (b6TwoPoint_sums 13 1 t.val.1 t.val.2 t.property).1
#print axioms Paper7MomentCounts.b6Theta252_row_qSums

theorem b6Theta252SingleRow_injective : Function.Injective b6Theta252SingleRow := by
  intro i j h
  by_contra hij
  have he := congrArg (fun x : PQ 6 => x.1 i) h
  simp [b6Theta252SingleRow,hij] at he
#print axioms Paper7MomentCounts.b6Theta252SingleRow_injective

theorem b6Theta252FullQRow_injective :
    Function.Injective (fun t : B6NinePair => b6Theta252FullQRow t.val.1 t.val.2) := by
  intro a b h
  have hi : a.val.1 = b.val.1 := by
    by_contra hn
    have he := congrArg (fun x : PQ 6 => x.2 a.val.1) h
    by_cases hab : a.val.1 = b.val.2
    · simp [b6Theta252FullQRow,b6TwoPoint,hab] at he
      exact hn (hab.trans he)
    · simp [b6Theta252FullQRow,b6TwoPoint,hn,hab] at he
  have hj : a.val.2 = b.val.2 := by
    by_contra hn
    have he := congrArg (fun x : PQ 6 => x.2 a.val.2) h
    have ha : a.val.2 ≠ a.val.1 := Ne.symm a.property
    have hb : a.val.2 ≠ b.val.1 := by simpa only [← hi] using ha
    simp [b6Theta252FullQRow,b6TwoPoint,ha,hb,hn] at he
  exact Subtype.ext (Prod.ext hi hj)
#print axioms Paper7MomentCounts.b6Theta252FullQRow_injective

def b6Theta252TemplateRow : Fin 6 ⊕ B6NinePair → PQ 6 :=
  Sum.elim b6Theta252SingleRow (fun t => b6Theta252FullQRow t.val.1 t.val.2)
#print axioms Paper7MomentCounts.b6Theta252TemplateRow

theorem b6Theta252TemplateRow_injective : Function.Injective b6Theta252TemplateRow := by
  unfold b6Theta252TemplateRow
  apply b6Theta252SingleRow_injective.sumElim b6Theta252FullQRow_injective
  intro a b he
  have hq := congrArg qSum he
  rw [b6Theta252_row_qSums.1,b6Theta252_row_qSums.2] at hq
  omega
#print axioms Paper7MomentCounts.b6Theta252TemplateRow_injective

theorem b6Theta252TemplateRow_accept (t : Fin 6 ⊕ B6NinePair) :
    b6CandidateGuard (b6Theta252TemplateRow t) ∧ theta (b6Theta252TemplateRow t) = 252 := by
  rcases t with t | t
  · exact b6Theta252SingleRow_accept t
  · exact b6Theta252FullQRow_accept t.val.1 t.val.2 t.property
#print axioms Paper7MomentCounts.b6Theta252TemplateRow_accept

def b6Theta252GuardEquiv :
    (Fin 6 ⊕ B6NinePair) ≃ {x : PQ 6 // b6CandidateGuard x ∧ theta x = 252} :=
  Equiv.ofBijective
    (fun t => ⟨b6Theta252TemplateRow t,b6Theta252TemplateRow_accept t⟩)
    ⟨fun _ _ h => b6Theta252TemplateRow_injective (congrArg Subtype.val h),by
      intro x
      rcases (b6_theta252_guard_iff x.val).mp x.property with
        ⟨i,hi⟩ | ⟨i,j,hij,he⟩
      · exact ⟨Sum.inl i,Subtype.ext hi.symm⟩
      · exact ⟨Sum.inr ⟨(i,j),hij⟩,Subtype.ext he.symm⟩⟩
#print axioms Paper7MomentCounts.b6Theta252GuardEquiv

def b6Theta252B1Equiv :
    (Fin 6 ⊕ B6NinePair) ≃ {x : PQ 6 // x ∈ CandB1 6 42 ∧ theta x = 252} :=
  b6Theta252GuardEquiv.trans (Equiv.subtypeEquivRight
    (fun x => and_congr (b6_candB1_iff_guard x).symm Iff.rfl))
#print axioms Paper7MomentCounts.b6Theta252B1Equiv

def b6Theta252D2Equiv :
    (Fin 6 ⊕ B6NinePair) ≃ {x : PQ 6 // x ∈ CandD2 6 42 ∧ theta x = 252} :=
  b6Theta252GuardEquiv.trans (Equiv.subtypeEquivRight
    (fun x => and_congr (b6_candD2_iff_guard x).symm Iff.rfl))
#print axioms Paper7MomentCounts.b6Theta252D2Equiv

theorem b6_theta252_candB1_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 252}.ncard = 36 := by
  change Nat.card {x : PQ 6 // x ∈ CandB1 6 42 ∧ theta x = 252} = 36
  rw [Nat.card_congr b6Theta252B1Equiv.symm]
  simp [Nat.card_eq_fintype_card,b6_nine_family_cards.1]
#print axioms Paper7MomentCounts.b6_theta252_candB1_ncard

theorem b6_theta252_candD2_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 252}.ncard = 36 := by
  change Nat.card {x : PQ 6 // x ∈ CandD2 6 42 ∧ theta x = 252} = 36
  rw [Nat.card_congr b6Theta252D2Equiv.symm]
  simp [Nat.card_eq_fintype_card,b6_nine_family_cards.1]
#print axioms Paper7MomentCounts.b6_theta252_candD2_ncard

end Paper7MomentCounts
