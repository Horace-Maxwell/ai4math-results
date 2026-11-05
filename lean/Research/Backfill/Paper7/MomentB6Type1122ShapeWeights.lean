import Research.Backfill.Paper7.MomentB6Type1122Coordinates

/-! Uncompiled true ordered-PQ shape fibres and their full q multiplicity.
Signs count ordered capacity placements; q fibres remain unsorted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b6Type1122CapacityOf (u : PQ 4) : Fin 4 → ℕ := fun i => u.1 i+u.2 i
#print axioms Paper7MomentCounts.b6Type1122CapacityOf

def b6Type1122HasShape (z : Fin 4 → ℕ) (A B D E : ℕ) : Prop :=
  (z 0+z 3=A ∧ max (z 0) (z 3)-min (z 0) (z 3)=D) ∧
    (z 1+z 2=B ∧ max (z 1) (z 2)-min (z 1) (z 2)=E)
#print axioms Paper7MomentCounts.b6Type1122HasShape

abbrev B6Type1122ShapeOriginalFibre (A B D E Q : ℕ) :=
  {u : PQ 4 // b6Type1122HasShape (b6Type1122CapacityOf u) A B D E ∧
    b6Type1122Total u.2=Q}
#print axioms Paper7MomentCounts.B6Type1122ShapeOriginalFibre

def b6Type1122ShapeCapacityEquiv (A B D E Q : ℕ) :
    B6Type1122ShapeOriginalFibre A B D E Q ≃
      Σ z : B6Type1122CapacityFibre A B D E,B6Type1122OriginalFibre z.val Q where
  toFun x := ⟨⟨b6Type1122CapacityOf x.val,x.property.1⟩,
    ⟨x.val,fun _ => rfl,x.property.2⟩⟩
  invFun x := ⟨x.2.val,by
    have hz : b6Type1122CapacityOf x.2.val=x.1.val := funext x.2.property.1
    exact ⟨hz.symm ▸ x.1.property,x.2.property.2⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    rcases x with ⟨⟨z,hz⟩,⟨u,hu⟩⟩
    have he : b6Type1122CapacityOf u=z := funext hu.1
    subst z
    rfl
#print axioms Paper7MomentCounts.b6Type1122ShapeCapacityEquiv

def b6Type1122ShapeSignEquiv (A B D E Q : ℕ)
    (hD : b6PairAdmissible A D) (hE : b6PairAdmissible B E) :
    B6Type1122ShapeOriginalFibre A B D E Q ≃
      Σ s : B6PairSign D × B6PairSign E,
        B6Type1122OriginalFibre (b6Type1122Restore A B D E s) Q :=
  (b6Type1122ShapeCapacityEquiv A B D E Q).trans
    (Equiv.sigmaCongrLeft (β := fun z : B6Type1122CapacityFibre A B D E =>
      B6Type1122OriginalFibre z.val Q) (b6Type1122CapacitySignEquiv A B D E hD hE)).symm
#print axioms Paper7MomentCounts.b6Type1122ShapeSignEquiv

instance b6Type1122OriginalFibreFinite (z : Fin 4 → ℕ) (Q : ℕ) :
    Finite (B6Type1122OriginalFibre z Q) :=
  Finite.of_injective (b6Type1122OriginalQEquiv z Q) (b6Type1122OriginalQEquiv z Q).injective
#print axioms Paper7MomentCounts.b6Type1122OriginalFibreFinite

def b6Type1122ShapeWeight (A B D E Q : ℕ) : ℕ :=
  (if D=0 then 1 else 2)*(if E=0 then 1 else 2)*
    b6Type1122Coefficient (b6PairHigh A D) (b6PairHigh B E)
      (b6PairLow B E) (b6PairLow A D) Q
#print axioms Paper7MomentCounts.b6Type1122ShapeWeight

theorem b6_type1122_shape_original_card (A B D E Q : ℕ)
    (hD : b6PairAdmissible A D) (hE : b6PairAdmissible B E) :
    Nat.card (B6Type1122ShapeOriginalFibre A B D E Q)=b6Type1122ShapeWeight A B D E Q := by
  rw [Nat.card_congr (b6Type1122ShapeSignEquiv A B D E Q hD hE),Nat.card_sigma]
  calc
    (∑ s : B6PairSign D × B6PairSign E,
      Nat.card (B6Type1122OriginalFibre (b6Type1122Restore A B D E s) Q)) =
      ∑ _s : B6PairSign D × B6PairSign E,
        b6Type1122Coefficient (b6PairHigh A D) (b6PairHigh B E)
          (b6PairLow B E) (b6PairLow A D) Q := by
      apply Finset.sum_congr rfl
      intro s _
      rw [b6_type1122_original_fibre_card,b6_type1122_restore_coefficient]
    _ = b6Type1122ShapeWeight A B D E Q := by simp [b6Type1122ShapeWeight,B6PairSign]
#print axioms Paper7MomentCounts.b6_type1122_shape_original_card

theorem b6_type1122_shape_admissible (A B D E Q : ℕ)
    (x : B6Type1122ShapeOriginalFibre A B D E Q) :
    b6PairAdmissible A D ∧ b6PairAdmissible B E := by
  have ha := b6_pair_admissible_of_ordered (b6Type1122CapacityOf x.val 0)
    (b6Type1122CapacityOf x.val 3)
  have hb := b6_pair_admissible_of_ordered (b6Type1122CapacityOf x.val 1)
    (b6Type1122CapacityOf x.val 2)
  exact ⟨by simpa only [x.property.1.1.1,x.property.1.1.2] using ha,
    by simpa only [x.property.1.2.1,x.property.1.2.2] using hb⟩
#print axioms Paper7MomentCounts.b6_type1122_shape_admissible

theorem b6_type1122_shape_total (A B D E Q : ℕ)
    (x : B6Type1122ShapeOriginalFibre A B D E Q) :
    b6Type1122Total (b6Type1122CapacityOf x.val)=A+2*B := by
  have ha := x.property.1.1.1
  have hb := x.property.1.2.1
  unfold b6Type1122Total
  omega
#print axioms Paper7MomentCounts.b6_type1122_shape_total

theorem b6_type1122_shape_moment_iff (A B D E Q : ℕ) (M : ℤ)
    (x : B6Type1122ShapeOriginalFibre A B D E Q) :
    theta (b6Type1122Row x.val)=M ↔
      (D : ℤ)^2+2*(E : ℤ)^2=b6Type1122SquareResidual A B Q M := by
  have ha := b6_type1122_shape_admissible A B D E Q x
  let z : B6Type1122CapacityFibre A B D E := ⟨b6Type1122CapacityOf x.val,x.property.1⟩
  obtain ⟨s,hs⟩ := (b6Type1122CapacitySignEquiv A B D E ha.1 ha.2).surjective z
  have hz : b6Type1122Restore A B D E s=b6Type1122CapacityOf x.val := congrArg Subtype.val hs
  have he := b6_type1122_moment_iff_norm A B D E Q M ha.1 ha.2 s
  rw [hz] at he
  have ht : theta (b6Type1122Row x.val)=
      12+3*(b6Type1122Total (b6Type1122CapacityOf x.val) : ℤ)+2*(Q : ℤ)+
        b6Type1122Squares (b6Type1122CapacityOf x.val) := by
    change theta (b6Type1122Row x.val)=
      12+3*(b6Type1122Total (fun i => x.val.1 i+x.val.2 i) : ℤ)+2*(Q : ℤ)+
        b6Type1122Squares (fun i => x.val.1 i+x.val.2 i)
    simpa only [x.property.2] using (b6_type1122_row_features x.val).2.2
  constructor
  · intro hM
    exact he.mp (hM.symm.trans ht)
  · intro hnorm
    exact ht.trans (he.mpr hnorm).symm
#print axioms Paper7MomentCounts.b6_type1122_shape_moment_iff

def b6Type1122OuterGuard (A B Q : ℕ) (M : ℤ) : Prop :=
  0 < A+2*B+Q ∧ A+2*B+Q ≤ 36 ∧ b6FeatureGuard (A+2*B+Q) Q M
#print axioms Paper7MomentCounts.b6Type1122OuterGuard

theorem b6_type1122_shape_accept_iff (A B D E Q : ℕ) (M : ℤ)
    (x : B6Type1122ShapeOriginalFibre A B D E Q)
    (hM : theta (b6Type1122Row x.val)=M) :
    b6Type1122Row x.val ∈ CandB1 6 42 ↔ b6Type1122OuterGuard A B Q M := by
  have hf := b6_type1122_row_features x.val
  have hw : weight (b6Type1122Row x.val)=A+2*B+Q := by
    rw [hf.1]
    change b6Type1122Total (b6Type1122CapacityOf x.val)+b6Type1122Total x.val.2=_
    rw [b6_type1122_shape_total A B D E Q x,x.property.2]
  have hq : qSum (b6Type1122Row x.val)=Q := hf.2.1.trans x.property.2
  rw [b6_candB1_iff_guard]
  unfold b6CandidateGuard b6Type1122OuterGuard
  rw [hw,hq,hM]
#print axioms Paper7MomentCounts.b6_type1122_shape_accept_iff

abbrev B6Type1122ShapeCell (A B D E Q : ℕ) (M : ℤ) :=
  {x : B6Type1122ShapeOriginalFibre A B D E Q //
    theta (b6Type1122Row x.val)=M ∧ b6Type1122Row x.val ∈ CandB1 6 42}
#print axioms Paper7MomentCounts.B6Type1122ShapeCell

theorem b6_type1122_shape_cell_conditions (A B D E Q : ℕ) (M : ℤ)
    (x : B6Type1122ShapeCell A B D E Q M) :
    b6PairAdmissible A D ∧ b6PairAdmissible B E ∧
      (D : ℤ)^2+2*(E : ℤ)^2=b6Type1122SquareResidual A B Q M ∧
      b6Type1122OuterGuard A B Q M := by
  have ha := b6_type1122_shape_admissible A B D E Q x.val
  exact ⟨ha.1,ha.2,(b6_type1122_shape_moment_iff A B D E Q M x.val).mp x.property.1,
    (b6_type1122_shape_accept_iff A B D E Q M x.val x.property.1).mp x.property.2⟩
#print axioms Paper7MomentCounts.b6_type1122_shape_cell_conditions

instance b6Type1122ShapeCellFinite (A B D E Q : ℕ) (M : ℤ) :
    Finite (B6Type1122ShapeCell A B D E Q M) := by
  apply Finite.of_injective
    (fun x : B6Type1122ShapeCell A B D E Q M =>
      (⟨x.val.val,x.property.2⟩ : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}))
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun u : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} => u.val) h
#print axioms Paper7MomentCounts.b6Type1122ShapeCellFinite

theorem b6_type1122_shape_cell_card (A B D E Q : ℕ) (M : ℤ) :
    Nat.card (B6Type1122ShapeCell A B D E Q M)=
      if b6PairAdmissible A D ∧ b6PairAdmissible B E ∧
        (D : ℤ)^2+2*(E : ℤ)^2=b6Type1122SquareResidual A B Q M ∧
        b6Type1122OuterGuard A B Q M then b6Type1122ShapeWeight A B D E Q else 0 := by
  by_cases h : b6PairAdmissible A D ∧ b6PairAdmissible B E ∧
      (D : ℤ)^2+2*(E : ℤ)^2=b6Type1122SquareResidual A B Q M ∧
      b6Type1122OuterGuard A B Q M
  · rw [ite_eq_left h]
    have hall (x : B6Type1122ShapeOriginalFibre A B D E Q) :
        theta (b6Type1122Row x.val)=M ∧ b6Type1122Row x.val ∈ CandB1 6 42 := by
      have hM := (b6_type1122_shape_moment_iff A B D E Q M x).mpr h.2.2.1
      exact ⟨hM,(b6_type1122_shape_accept_iff A B D E Q M x hM).mpr h.2.2.2⟩
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall)]
    exact b6_type1122_shape_original_card A B D E Q h.1 h.2.1
  · rw [ite_eq_right h]
    let : IsEmpty (B6Type1122ShapeCell A B D E Q M) :=
      ⟨fun x => h (b6_type1122_shape_cell_conditions A B D E Q M x)⟩
    exact Nat.card_of_isEmpty
#print axioms Paper7MomentCounts.b6_type1122_shape_cell_card

end Paper7MomentCounts
