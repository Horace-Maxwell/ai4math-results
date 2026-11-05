import Research.Backfill.Paper7.MomentB6Type1122Partition

/-! Uncompiled exact ordered-pair restoration. Zero difference has one sign;
positive difference has two signs. No finite numerical enumeration is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

def b6PairAdmissible (A D : ℕ) : Prop := D ≤ A ∧ A % 2 = D % 2
#print axioms Paper7MomentCounts.b6PairAdmissible

def b6PairHigh (A D : ℕ) : ℕ := (A+D)/2
#print axioms Paper7MomentCounts.b6PairHigh

def b6PairLow (A D : ℕ) : ℕ := (A-D)/2
#print axioms Paper7MomentCounts.b6PairLow

abbrev B6PairSign (D : ℕ) := Fin (if D=0 then 1 else 2)
#print axioms Paper7MomentCounts.B6PairSign

def b6PairRestore (A D : ℕ) (s : B6PairSign D) : ℕ × ℕ :=
  if s.val=0 then (b6PairHigh A D,b6PairLow A D)
    else (b6PairLow A D,b6PairHigh A D)
#print axioms Paper7MomentCounts.b6PairRestore

abbrev B6PairCoordinateFibre (A D : ℕ) :=
  {x : ℕ × ℕ // x.1+x.2=A ∧ max x.1 x.2-min x.1 x.2=D}
#print axioms Paper7MomentCounts.B6PairCoordinateFibre

theorem b6_pair_half_arithmetic (A D : ℕ) (h : b6PairAdmissible A D) :
    b6PairHigh A D+b6PairLow A D=A ∧
    b6PairHigh A D-b6PairLow A D=D ∧
    b6PairLow A D ≤ b6PairHigh A D := by
  unfold b6PairAdmissible at h
  unfold b6PairHigh b6PairLow
  omega
#print axioms Paper7MomentCounts.b6_pair_half_arithmetic

theorem b6_pair_sign_bounds (D : ℕ) (s : B6PairSign D) :
    s.val < 2 ∧ (D=0 → s.val=0) := by
  have hs := s.isLt
  by_cases h : D=0
  · simp only [h,ite_true] at hs
    omega
  · simp only [h,ite_false] at hs
    exact ⟨hs,fun h0 => (h h0).elim⟩
#print axioms Paper7MomentCounts.b6_pair_sign_bounds

theorem b6_pair_admissible_of_ordered (x y : ℕ) :
    b6PairAdmissible (x+y) (max x y-min x y) := by
  unfold b6PairAdmissible
  rcases le_total x y with h | h
  · rw [max_eq_right h,min_eq_left h]
    omega
  · rw [max_eq_left h,min_eq_right h]
    omega
#print axioms Paper7MomentCounts.b6_pair_admissible_of_ordered

theorem b6_pair_restore_features (A D : ℕ) (h : b6PairAdmissible A D)
    (s : B6PairSign D) :
    (b6PairRestore A D s).1+(b6PairRestore A D s).2=A ∧
      max (b6PairRestore A D s).1 (b6PairRestore A D s).2-
        min (b6PairRestore A D s).1 (b6PairRestore A D s).2=D := by
  have hh := b6_pair_half_arithmetic A D h
  by_cases hs : s.val=0
  · simpa [b6PairRestore,hs,max_eq_left hh.2.2,min_eq_right hh.2.2] using
      ⟨hh.1,hh.2.1⟩
  · simpa [b6PairRestore,hs,max_eq_right hh.2.2,min_eq_left hh.2.2,add_comm] using
      ⟨hh.1,hh.2.1⟩
#print axioms Paper7MomentCounts.b6_pair_restore_features

theorem b6_pair_restore_injective (A D : ℕ) (h : b6PairAdmissible A D) :
    Function.Injective (b6PairRestore A D) := by
  intro s t he
  have hs := b6_pair_sign_bounds D s
  have ht := b6_pair_sign_bounds D t
  have hh := b6_pair_half_arithmetic A D h
  apply Fin.ext
  by_cases hs0 : s.val=0 <;> by_cases ht0 : t.val=0
  · omega
  · have hp := congrArg Prod.fst he
    simp only [b6PairRestore,hs0,ht0,ite_true,ite_false] at hp
    have hD : D=0 := by omega
    exact (ht0 (ht.2 hD)).elim
  · have hp := congrArg Prod.fst he
    simp only [b6PairRestore,hs0,ht0,ite_true,ite_false] at hp
    have hD : D=0 := by omega
    exact (hs0 (hs.2 hD)).elim
  · omega
#print axioms Paper7MomentCounts.b6_pair_restore_injective

theorem b6_pair_restore_surjective (A D : ℕ) (h : b6PairAdmissible A D)
    (x : B6PairCoordinateFibre A D) : ∃ s : B6PairSign D,b6PairRestore A D s=x.val := by
  have hx := x.property
  have hh := b6_pair_half_arithmetic A D h
  by_cases ho : x.val.2 ≤ x.val.1
  · rw [max_eq_left ho,min_eq_right ho] at hx
    let s : B6PairSign D := ⟨0,by by_cases hD : D=0 <;> simp [hD]⟩
    refine ⟨s,?_⟩
    have hp : x.val.1=b6PairHigh A D ∧ x.val.2=b6PairLow A D := by omega
    apply Prod.ext <;> simp [b6PairRestore,s,hp.1,hp.2]
  · have ho' : x.val.1 ≤ x.val.2 := by omega
    rw [max_eq_right ho',min_eq_left ho'] at hx
    have hD : D≠0 := by omega
    let s : B6PairSign D := ⟨1,by simp [hD]⟩
    refine ⟨s,?_⟩
    have hp : x.val.1=b6PairLow A D ∧ x.val.2=b6PairHigh A D := by omega
    apply Prod.ext <;> simp [b6PairRestore,s,hp.1,hp.2]
#print axioms Paper7MomentCounts.b6_pair_restore_surjective

def b6PairCoordinateEquiv (A D : ℕ) (h : b6PairAdmissible A D) :
    B6PairSign D ≃ B6PairCoordinateFibre A D :=
  Equiv.ofBijective (fun s => ⟨b6PairRestore A D s,b6_pair_restore_features A D h s⟩)
    ⟨fun _ _ he => b6_pair_restore_injective A D h (congrArg Subtype.val he),by
      intro x
      obtain ⟨s,hs⟩ := b6_pair_restore_surjective A D h x
      exact ⟨s,Subtype.ext hs⟩⟩
#print axioms Paper7MomentCounts.b6PairCoordinateEquiv

theorem b6_pair_coordinate_fibre_card (A D : ℕ) (h : b6PairAdmissible A D) :
    Nat.card (B6PairCoordinateFibre A D) = if D=0 then 1 else 2 := by
  rw [Nat.card_congr (b6PairCoordinateEquiv A D h).symm]
  simp [B6PairSign]
#print axioms Paper7MomentCounts.b6_pair_coordinate_fibre_card

def b6TwoBoundedQSwap (a d s : ℕ) : B6TwoBoundedQ a d s ≃ B6TwoBoundedQ d a s where
  toFun q := ⟨(q.val.2,q.val.1),by
    change q.val.2.val+q.val.1.val=s
    exact (Nat.add_comm _ _).trans q.property⟩
  invFun q := ⟨(q.val.2,q.val.1),by
    change q.val.2.val+q.val.1.val=s
    exact (Nat.add_comm _ _).trans q.property⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl
#print axioms Paper7MomentCounts.b6TwoBoundedQSwap

theorem b6_interval_multiplicity_swap (a d s : ℕ) :
    b6IntervalMultiplicity a d s=b6IntervalMultiplicity d a s := by
  rw [← b6_two_bounded_q_card,← b6_two_bounded_q_card]
  exact Nat.card_congr (b6TwoBoundedQSwap a d s)
#print axioms Paper7MomentCounts.b6_interval_multiplicity_swap

theorem b6_pair_restore_interval (A D : ℕ) (s : B6PairSign D) (q : ℕ) :
    b6IntervalMultiplicity (b6PairRestore A D s).1 (b6PairRestore A D s).2 q =
      b6IntervalMultiplicity (b6PairHigh A D) (b6PairLow A D) q := by
  by_cases hs : s.val=0
  · simp [b6PairRestore,hs]
  · simpa [b6PairRestore,hs] using
      b6_interval_multiplicity_swap (b6PairLow A D) (b6PairHigh A D) q
#print axioms Paper7MomentCounts.b6_pair_restore_interval

end Paper7MomentCounts
