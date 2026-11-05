import Research.Backfill.Paper7.MomentB6PairCoordinates

/-! Uncompiled shape-fibre bijections and the exact quadratic identity.
The two singleton positions and both doubled positions stay labelled. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

def b6Type1122Restore (A B D E : ℕ) (s : B6PairSign D × B6PairSign E) : Fin 4 → ℕ :=
  ![(b6PairRestore A D s.1).1,(b6PairRestore B E s.2).1,
    (b6PairRestore B E s.2).2,(b6PairRestore A D s.1).2]
#print axioms Paper7MomentCounts.b6Type1122Restore

abbrev B6Type1122CapacityFibre (A B D E : ℕ) :=
  {z : Fin 4 → ℕ // (z 0+z 3=A ∧ max (z 0) (z 3)-min (z 0) (z 3)=D) ∧
    (z 1+z 2=B ∧ max (z 1) (z 2)-min (z 1) (z 2)=E)}
#print axioms Paper7MomentCounts.B6Type1122CapacityFibre

def b6Type1122CapacityPairEquiv (A B D E : ℕ) :
    B6Type1122CapacityFibre A B D E ≃
      B6PairCoordinateFibre A D × B6PairCoordinateFibre B E where
  toFun z := (⟨(z.val 0,z.val 3),z.property.1⟩,⟨(z.val 1,z.val 2),z.property.2⟩)
  invFun p := ⟨![p.1.val.1,p.2.val.1,p.2.val.2,p.1.val.2],p.1.property,p.2.property⟩
  left_inv z := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv p := by apply Prod.ext <;> apply Subtype.ext <;> rfl
#print axioms Paper7MomentCounts.b6Type1122CapacityPairEquiv

def b6Type1122CapacitySignEquiv (A B D E : ℕ)
    (hD : b6PairAdmissible A D) (hE : b6PairAdmissible B E) :
    (B6PairSign D × B6PairSign E) ≃ B6Type1122CapacityFibre A B D E :=
  (Equiv.prodCongr (b6PairCoordinateEquiv A D hD) (b6PairCoordinateEquiv B E hE)).trans
    (b6Type1122CapacityPairEquiv A B D E).symm
#print axioms Paper7MomentCounts.b6Type1122CapacitySignEquiv

theorem b6_type1122_capacity_sign_value (A B D E : ℕ)
    (hD : b6PairAdmissible A D) (hE : b6PairAdmissible B E)
    (s : B6PairSign D × B6PairSign E) :
    (b6Type1122CapacitySignEquiv A B D E hD hE s).val=b6Type1122Restore A B D E s := rfl
#print axioms Paper7MomentCounts.b6_type1122_capacity_sign_value

theorem b6_type1122_capacity_fibre_card (A B D E : ℕ)
    (hD : b6PairAdmissible A D) (hE : b6PairAdmissible B E) :
    Nat.card (B6Type1122CapacityFibre A B D E)=
      (if D=0 then 1 else 2)*(if E=0 then 1 else 2) := by
  rw [Nat.card_congr (b6Type1122CapacitySignEquiv A B D E hD hE).symm,Nat.card_prod]
  simp [B6PairSign]
#print axioms Paper7MomentCounts.b6_type1122_capacity_fibre_card

theorem b6_pair_restore_square_identity (A D : ℕ) (hD : b6PairAdmissible A D)
    (s : B6PairSign D) :
    2*((b6PairRestore A D s).1 : ℤ)^2+2*((b6PairRestore A D s).2 : ℤ)^2=
      (A : ℤ)^2+(D : ℤ)^2 := by
  have hh := b6_pair_half_arithmetic A D hD
  have hs : (A : ℤ)=(b6PairHigh A D : ℤ)+(b6PairLow A D : ℤ) := by
    exact_mod_cast hh.1.symm
  have hn : D+b6PairLow A D=b6PairHigh A D := by omega
  have hd : (D : ℤ)=(b6PairHigh A D : ℤ)-(b6PairLow A D : ℤ) := by
    have hc : (D : ℤ)+(b6PairLow A D : ℤ)=(b6PairHigh A D : ℤ) := by exact_mod_cast hn
    omega
  rw [hs,hd]
  by_cases hz : s.val=0 <;> simp only [b6PairRestore,hz,ite_true,ite_false] <;> ring
#print axioms Paper7MomentCounts.b6_pair_restore_square_identity

theorem b6_type1122_restore_total (A B D E : ℕ)
    (hD : b6PairAdmissible A D) (hE : b6PairAdmissible B E)
    (s : B6PairSign D × B6PairSign E) :
    b6Type1122Total (b6Type1122Restore A B D E s)=A+2*B := by
  have ha := (b6_pair_restore_features A D hD s.1).1
  have hb := (b6_pair_restore_features B E hE s.2).1
  dsimp [b6Type1122Total,b6Type1122Restore]
  omega
#print axioms Paper7MomentCounts.b6_type1122_restore_total

theorem b6_type1122_restore_square_identity (A B D E : ℕ)
    (hD : b6PairAdmissible A D) (hE : b6PairAdmissible B E)
    (s : B6PairSign D × B6PairSign E) :
    2*b6Type1122Squares (b6Type1122Restore A B D E s)=
      (A : ℤ)^2+(D : ℤ)^2+2*(B : ℤ)^2+2*(E : ℤ)^2 := by
  have ha := b6_pair_restore_square_identity A D hD s.1
  have hb := b6_pair_restore_square_identity B E hE s.2
  dsimp [b6Type1122Squares,b6Type1122Restore]
  nlinarith only [ha,hb]
#print axioms Paper7MomentCounts.b6_type1122_restore_square_identity

def b6Type1122SquareResidual (A B Q : ℕ) (M : ℤ) : ℤ :=
  2*M-24-6*(A : ℤ)-12*(B : ℤ)-4*(Q : ℤ)-(A : ℤ)^2-2*(B : ℤ)^2
#print axioms Paper7MomentCounts.b6Type1122SquareResidual

theorem b6_type1122_moment_iff_norm (A B D E Q : ℕ) (M : ℤ)
    (hD : b6PairAdmissible A D) (hE : b6PairAdmissible B E)
    (s : B6PairSign D × B6PairSign E) :
    M=12+3*(b6Type1122Total (b6Type1122Restore A B D E s) : ℤ)+2*(Q : ℤ)+
      b6Type1122Squares (b6Type1122Restore A B D E s) ↔
    (D : ℤ)^2+2*(E : ℤ)^2=b6Type1122SquareResidual A B Q M := by
  rw [b6_type1122_restore_total A B D E hD hE s]
  have hsq := b6_type1122_restore_square_identity A B D E hD hE s
  unfold b6Type1122SquareResidual
  push_cast
  constructor <;> intro hm <;> nlinarith only [hsq,hm]
#print axioms Paper7MomentCounts.b6_type1122_moment_iff_norm

def b6Type1122CompressedGuard (A B D E Q : ℕ) : Prop :=
  0 < A+2*B+Q ∧ A+2*B+Q ≤ 36 ∧
    ∃ sm ∈ b6FeatureCatalog,
      (D : ℤ)^2+2*(E : ℤ)^2=b6Type1122SquareResidual A B Q sm.2 ∧
      sm.1 ≤ (6+(A+2*B+Q : ℕ) : ℤ) ∧
      (6+(A+2*B+Q : ℕ) : ℤ)-max (Q : ℤ) 2 ≤ sm.1
#print axioms Paper7MomentCounts.b6Type1122CompressedGuard

theorem b6_type1122_restore_guard_iff (A B D E Q : ℕ)
    (hD : b6PairAdmissible A D) (hE : b6PairAdmissible B E)
    (s : B6PairSign D × B6PairSign E) :
    b6Type1122Guard (b6Type1122Restore A B D E s) Q ↔
      b6Type1122CompressedGuard A B D E Q := by
  unfold b6Type1122Guard b6FeatureGuard b6Type1122CompressedGuard
  rw [b6_type1122_restore_total A B D E hD hE s]
  constructor
  · rintro ⟨hw,hb,sm,hsm,hm,hs,hl⟩
    have he := b6_type1122_moment_iff_norm A B D E Q sm.2 hD hE s
    rw [b6_type1122_restore_total A B D E hD hE s] at he
    exact ⟨hw,hb,sm,hsm,he.mp hm,hs,hl⟩
  · rintro ⟨hw,hb,sm,hsm,hm,hs,hl⟩
    have he := b6_type1122_moment_iff_norm A B D E Q sm.2 hD hE s
    rw [b6_type1122_restore_total A B D E hD hE s] at he
    exact ⟨hw,hb,sm,hsm,he.mpr hm,hs,hl⟩
#print axioms Paper7MomentCounts.b6_type1122_restore_guard_iff

theorem b6_type1122_restore_coefficient (A B D E Q : ℕ)
    (s : B6PairSign D × B6PairSign E) :
    b6Type1122Coefficient (b6Type1122Restore A B D E s 0)
      (b6Type1122Restore A B D E s 1) (b6Type1122Restore A B D E s 2)
      (b6Type1122Restore A B D E s 3) Q =
    b6Type1122Coefficient (b6PairHigh A D) (b6PairHigh B E)
      (b6PairLow B E) (b6PairLow A D) Q := by
  unfold b6Type1122Coefficient
  apply Finset.sum_congr rfl
  intro t _
  change b6IntervalMultiplicity (b6PairRestore A D s.1).1 (b6PairRestore A D s.1).2
      (Q-2*t.val) *
    b6IntervalMultiplicity (b6PairRestore B E s.2).1 (b6PairRestore B E s.2).2 t.val = _
  rw [b6_pair_restore_interval,b6_pair_restore_interval]
#print axioms Paper7MomentCounts.b6_type1122_restore_coefficient

end Paper7MomentCounts
