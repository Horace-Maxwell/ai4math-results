import Research.Backfill.Paper7.MomentB6Type1122ShapeWeights
import Research.Backfill.Paper7.MomentB6Type1122SquareTest

/-! Uncompiled exact per-moment layer count. E is recovered by a single
integer square discriminator for each D; no rectangular sum is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

abbrev B6Type1122Layer (A B Q : ℕ) (M : ℤ) :=
  {u : PQ 4 // (b6Type1122CapacityOf u 0+b6Type1122CapacityOf u 3=A) ∧
    (b6Type1122CapacityOf u 1+b6Type1122CapacityOf u 2=B) ∧
    b6Type1122Total u.2=Q ∧ theta (b6Type1122Row u)=M ∧
    b6Type1122Row u ∈ CandB1 6 42}
#print axioms Paper7MomentCounts.B6Type1122Layer

def b6Type1122DifferenceIndex (A B Q : ℕ) (M : ℤ)
    (x : B6Type1122Layer A B Q M) : Fin (A+1) × Fin (B+1) := by
  have ha := x.property.1
  have hb := x.property.2.1
  exact (⟨max (b6Type1122CapacityOf x.val 0) (b6Type1122CapacityOf x.val 3)-
      min (b6Type1122CapacityOf x.val 0) (b6Type1122CapacityOf x.val 3),by omega⟩,
    ⟨max (b6Type1122CapacityOf x.val 1) (b6Type1122CapacityOf x.val 2)-
      min (b6Type1122CapacityOf x.val 1) (b6Type1122CapacityOf x.val 2),by omega⟩)
#print axioms Paper7MomentCounts.b6Type1122DifferenceIndex

def b6Type1122DifferenceFibreEquiv (A B Q : ℕ) (M : ℤ)
    (r : Fin (A+1) × Fin (B+1)) :
    {x : B6Type1122Layer A B Q M // b6Type1122DifferenceIndex A B Q M x=r} ≃
      B6Type1122ShapeCell A B r.1.val r.2.val Q M where
  toFun x := by
    have hD := congrArg (fun y : Fin (A+1) × Fin (B+1) => y.1.val) x.property
    have hE := congrArg (fun y : Fin (A+1) × Fin (B+1) => y.2.val) x.property
    exact ⟨⟨x.val.val,⟨⟨x.val.property.1,hD⟩,⟨x.val.property.2.1,hE⟩⟩,
      x.val.property.2.2.1⟩,x.val.property.2.2.2⟩
  invFun x := by
    let u : B6Type1122Layer A B Q M :=
      ⟨x.val.val,x.val.property.1.1.1,x.val.property.1.2.1,x.val.property.2,x.property⟩
    refine ⟨u,?_⟩
    apply Prod.ext
    · exact Fin.ext x.val.property.1.1.2
    · exact Fin.ext x.val.property.1.2.2
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
#print axioms Paper7MomentCounts.b6Type1122DifferenceFibreEquiv

instance b6Type1122LayerFinite (A B Q : ℕ) (M : ℤ) : Finite (B6Type1122Layer A B Q M) := by
  apply Finite.of_injective
    (fun x : B6Type1122Layer A B Q M =>
      (⟨x.val,x.property.2.2.2.2⟩ : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}))
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} => z.val) h
#print axioms Paper7MomentCounts.b6Type1122LayerFinite

def b6Type1122LayerSquareSum (A B Q : ℕ) (M : ℤ) : ℕ :=
  if b6Type1122OuterGuard A B Q M then
    ∑ d : Fin (A+1),
      if A % 2=d.val % 2 then
        if b6Type1122SquareTest d.val B (b6Type1122SquareResidual A B Q M) then
          b6Type1122ShapeWeight A B d.val
            (b6Type1122SquareE d.val (b6Type1122SquareResidual A B Q M)) Q
        else 0
      else 0
  else 0
#print axioms Paper7MomentCounts.b6Type1122LayerSquareSum

theorem b6_type1122_shape_sum_eliminate_E (A B Q : ℕ) (M : ℤ) :
    (∑ r : Fin (A+1) × Fin (B+1),
      if b6PairAdmissible A r.1.val ∧ b6PairAdmissible B r.2.val ∧
        (r.1.val : ℤ)^2+2*(r.2.val : ℤ)^2=b6Type1122SquareResidual A B Q M ∧
        b6Type1122OuterGuard A B Q M then
          b6Type1122ShapeWeight A B r.1.val r.2.val Q else 0)=
      b6Type1122LayerSquareSum A B Q M := by
  unfold b6Type1122LayerSquareSum
  rw [Fintype.sum_prod_type]
  by_cases ho : b6Type1122OuterGuard A B Q M
  · rw [ite_eq_left ho]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hp : A % 2=d.val % 2
    · rw [ite_eq_left hp]
      have hD : b6PairAdmissible A d.val := ⟨Nat.le_of_lt_succ d.isLt,hp⟩
      have hiff (e : Fin (B+1)) :
          (b6PairAdmissible A d.val ∧ b6PairAdmissible B e.val ∧
            (d.val : ℤ)^2+2*(e.val : ℤ)^2=b6Type1122SquareResidual A B Q M ∧
            b6Type1122OuterGuard A B Q M) ↔
          ((d.val : ℤ)^2+2*(e.val : ℤ)^2=b6Type1122SquareResidual A B Q M ∧
            e.val % 2=B % 2) := by
        constructor
        · intro h
          exact ⟨h.2.2.1,h.2.1.2.symm⟩
        · intro h
          exact ⟨hD,⟨Nat.le_of_lt_succ e.isLt,h.2.symm⟩,h.1,ho⟩
      simp_rw [hiff]
      exact b6_type1122_square_weighted_sum d.val B (b6Type1122SquareResidual A B Q M)
        (fun E => b6Type1122ShapeWeight A B d.val E Q)
    · rw [ite_eq_right hp]
      apply Finset.sum_eq_zero
      intro e _
      exact ite_eq_right (fun h => hp h.1.2)
  · rw [ite_eq_right ho]
    apply Finset.sum_eq_zero
    intro d _
    apply Finset.sum_eq_zero
    intro e _
    exact ite_eq_right (fun h => ho h.2.2.2)
#print axioms Paper7MomentCounts.b6_type1122_shape_sum_eliminate_E

theorem b6_type1122_layer_card_eq_square_sum (A B Q : ℕ) (M : ℤ) :
    Nat.card (B6Type1122Layer A B Q M)=b6Type1122LayerSquareSum A B Q M := by
  let e := (Equiv.sigmaFiberEquiv (b6Type1122DifferenceIndex A B Q M)).symm.trans
    (Equiv.sigmaCongrRight (b6Type1122DifferenceFibreEquiv A B Q M))
  rw [Nat.card_congr e,Nat.card_sigma]
  calc
    (∑ r : Fin (A+1) × Fin (B+1),Nat.card (B6Type1122ShapeCell A B r.1.val r.2.val Q M)) =
      ∑ r : Fin (A+1) × Fin (B+1),
        if b6PairAdmissible A r.1.val ∧ b6PairAdmissible B r.2.val ∧
          (r.1.val : ℤ)^2+2*(r.2.val : ℤ)^2=b6Type1122SquareResidual A B Q M ∧
          b6Type1122OuterGuard A B Q M then
            b6Type1122ShapeWeight A B r.1.val r.2.val Q else 0 := by
      exact Finset.sum_congr rfl (fun r _ => b6_type1122_shape_cell_card A B r.1.val r.2.val Q M)
    _ = b6Type1122LayerSquareSum A B Q M := b6_type1122_shape_sum_eliminate_E A B Q M
#print axioms Paper7MomentCounts.b6_type1122_layer_card_eq_square_sum

theorem b6_type1122_norm_Q_recovery (A B D E Q : ℕ) (M : ℤ)
    (h : (D : ℤ)^2+2*(E : ℤ)^2=b6Type1122SquareResidual A B Q M) :
    4*(Q : ℤ)=2*M-24-6*(A : ℤ)-12*(B : ℤ)-(A : ℤ)^2-2*(B : ℤ)^2-
      (D : ℤ)^2-2*(E : ℤ)^2 := by
  unfold b6Type1122SquareResidual at h
  linarith
#print axioms Paper7MomentCounts.b6_type1122_norm_Q_recovery

theorem b6_type1122_outer_guard_load_ranges (A B Q : ℕ) (M : ℤ)
    (h : b6Type1122OuterGuard A B Q M) :
    ∃ sm ∈ b6FeatureCatalog,sm.2=M ∧
      (Q ≤ 1 → sm.1-6-(Q : ℤ) ≤ (A : ℤ)+2*(B : ℤ) ∧
        (A : ℤ)+2*(B : ℤ) ≤ sm.1-4-(Q : ℤ)) ∧
      (2 ≤ Q → sm.1-6-(Q : ℤ) ≤ (A : ℤ)+2*(B : ℤ) ∧
        (A : ℤ)+2*(B : ℤ) ≤ sm.1-6) := by
  obtain ⟨sm,hsm,hM,hs,hl⟩ := h.2.2
  push_cast at hs hl
  refine ⟨sm,hsm,hM,?_,?_⟩
  · intro hQ
    have hQI : (Q : ℤ) ≤ 2 := by omega
    rw [max_eq_right hQI] at hl
    omega
  · intro hQ
    have hQI : (2 : ℤ) ≤ Q := by exact_mod_cast hQ
    rw [max_eq_left hQI] at hl
    omega
#print axioms Paper7MomentCounts.b6_type1122_outer_guard_load_ranges

theorem b6_type1122_square_test_D_bound (A D B : ℕ) (R : ℤ)
    (hD : D ≤ A) (h : b6Type1122SquareTest D B R) :
    0 ≤ R ∧ D ≤ min A (Nat.sqrt R.toNat) := by
  have he := (b6_type1122_square_from_test D B R h).1
  have hs := sq_nonneg (b6Type1122SquareE D R : ℤ)
  have hds := sq_nonneg (D : ℤ)
  have hR : 0 ≤ R := by nlinarith only [he,hs,hds]
  have hd : (D : ℤ)^2 ≤ R := by nlinarith only [he,hs]
  have hdN : D^2 ≤ R.toNat := by
    have heR : (R.toNat : ℤ)=R := Int.toNat_of_nonneg hR
    rw [← heR] at hd
    exact_mod_cast hd
  exact ⟨hR,le_min hD (Nat.le_sqrt'.mpr hdN)⟩
#print axioms Paper7MomentCounts.b6_type1122_square_test_D_bound

end Paper7MomentCounts
