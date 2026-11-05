import Research.Backfill.Paper7.MomentB6Type1122WindowPartition

/-! Pending constructive arithmetic interface for the exact original1122 count.
The finite windows are derived from the original fibre. Closed arithmetic can
later be checked one catalogue/mass/pair-sum/Q block at a time. No block or total
is evaluated here; no broad rectangular index occurs in these definitions. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

/-- Primitive arithmetic copy: no classical existential guard is evaluated. -/
def b6Type1122WindowResidual (A B Q : ℕ) (M : ℤ) : ℤ :=
  2*M-24-6*(A : ℤ)-12*(B : ℤ)-4*(Q : ℤ)-(A : ℤ)^2-2*(B : ℤ)^2
#print axioms Paper7MomentCounts.b6Type1122WindowResidual

def b6Type1122WindowWeight (A B D E Q : ℕ) : ℕ :=
  (if D=0 then 1 else 2)*(if E=0 then 1 else 2)*
    ∑ t : Fin (Q/2+1),
      (min ((A+D)/2) (Q-2*t.val)+1-((Q-2*t.val)-(A-D)/2))*
        (min ((B+E)/2) t.val+1-(t.val-(B-E)/2))
#print axioms Paper7MomentCounts.b6Type1122WindowWeight

theorem b6_type1122_window_weight_eq (A B D E Q : ℕ) :
    b6Type1122WindowWeight A B D E Q=b6Type1122ShapeWeight A B D E Q := by
  classical
  by_cases hD : D=0 <;> by_cases hE : E=0 <;>
    simp [b6Type1122WindowWeight,b6Type1122ShapeWeight,hD,hE,
      b6Type1122Coefficient,b6IntervalMultiplicity,b6PairHigh,b6PairLow]
#print axioms Paper7MomentCounts.b6_type1122_window_weight_eq

def b6Type1122WindowTerm (A B Q : ℕ) (M : ℤ) : ℕ :=
  ∑ d : Fin (A+1),
    if A % 2=d.val % 2 then
      if b6Type1122SquareTest d.val B (b6Type1122WindowResidual A B Q M) then
        b6Type1122WindowWeight A B d.val
          (b6Type1122SquareE d.val (b6Type1122WindowResidual A B Q M)) Q
      else 0
    else 0
#print axioms Paper7MomentCounts.b6Type1122WindowTerm

theorem b6_type1122_window_term_eq_layer (A B Q : ℕ) (M : ℤ)
    (hg : b6Type1122OuterGuard A B Q M) :
    b6Type1122WindowTerm A B Q M=b6Type1122LayerSquareSum A B Q M := by
  classical
  unfold b6Type1122LayerSquareSum
  rw [ite_eq_left hg]
  unfold b6Type1122WindowTerm
  apply Finset.sum_congr rfl
  intro d _
  have hR : b6Type1122WindowResidual A B Q M=b6Type1122SquareResidual A B Q M := rfl
  rw [hR]
  by_cases hp : A % 2=d.val % 2
  · by_cases ht : b6Type1122SquareTest d.val B (b6Type1122SquareResidual A B Q M)
    · simpa only [ite_eq_left hp,ite_eq_left ht] using b6_type1122_window_weight_eq A B d.val
        (b6Type1122SquareE d.val (b6Type1122SquareResidual A B Q M)) Q
    · simp only [ite_eq_left hp,ite_eq_right ht]
  · simp only [ite_eq_right hp]
#print axioms Paper7MomentCounts.b6_type1122_window_term_eq_layer

/-- A supported D recovers exactly one E, and that shape recovers exactly one Q. -/
theorem b6_type1122_window_square_recovery (A B D Q : ℕ) (M : ℤ)
    (hD : D ≤ A)
    (ht : b6Type1122SquareTest D B (b6Type1122WindowResidual A B Q M)) :
    let E := b6Type1122SquareE D (b6Type1122WindowResidual A B Q M)
    E ≤ B ∧ E % 2=B % 2 ∧
      D ≤ min A (Nat.sqrt (b6Type1122WindowResidual A B Q M).toNat) ∧
      4*(Q : ℤ)=2*M-24-6*(A : ℤ)-12*(B : ℤ)-(A : ℤ)^2-2*(B : ℤ)^2-
        (D : ℤ)^2-2*(E : ℤ)^2 := by
  have he := b6_type1122_square_from_test D B (b6Type1122WindowResidual A B Q M) ht
  have hb := b6_type1122_square_test_D_bound A D B _ hD ht
  exact ⟨he.2.1,he.2.2,hb.2,b6_type1122_norm_Q_recovery A B D _ Q M he.1⟩
#print axioms Paper7MomentCounts.b6_type1122_window_square_recovery

theorem b6_type1122_window_Q_unique (A B D E Q Q' : ℕ) (M : ℤ)
    (h : (D : ℤ)^2+2*(E : ℤ)^2=b6Type1122WindowResidual A B Q M)
    (h' : (D : ℤ)^2+2*(E : ℤ)^2=b6Type1122WindowResidual A B Q' M) : Q=Q' := by
  unfold b6Type1122WindowResidual at h h'
  omega
#print axioms Paper7MomentCounts.b6_type1122_window_Q_unique

/-- This block has only the derived Q interval; each Q term has one D sum. -/
def b6Type1122WindowQBlock (sm : ↥b6FeatureCatalog)
    (Z : ↥(b6Type1122MassWindow sm.val.1 sm.val.2)) (B : Fin (Z.val/2+1)) : ℕ :=
  ∑ Q : ↥(Finset.Icc (b6Type1122QLower (b6Type1122LoadCenter sm.val.1) Z.val)
      (b6Type1122QUpper (b6Type1122LoadCenter sm.val.1) Z.val)),
    b6Type1122WindowTerm (Z.val-2*B.val) B.val Q.val sm.val.2
#print axioms Paper7MomentCounts.b6Type1122WindowQBlock

def b6Type1122WindowMassBlock (sm : ↥b6FeatureCatalog)
    (Z : ↥(b6Type1122MassWindow sm.val.1 sm.val.2)) : ℕ :=
  ∑ B : Fin (Z.val/2+1),b6Type1122WindowQBlock sm Z B
#print axioms Paper7MomentCounts.b6Type1122WindowMassBlock

def b6Type1122WindowCatalogBlock (sm : ↥b6FeatureCatalog) : ℕ :=
  ∑ Z : ↥(b6Type1122MassWindow sm.val.1 sm.val.2),b6Type1122WindowMassBlock sm Z
#print axioms Paper7MomentCounts.b6Type1122WindowCatalogBlock

def b6Type1122WindowCount : ℕ :=
  ∑ sm : ↥b6FeatureCatalog,b6Type1122WindowCatalogBlock sm
#print axioms Paper7MomentCounts.b6Type1122WindowCount

theorem b6_type1122_original_count_eq_window_sum :
    Nat.card {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}=b6Type1122WindowCount := by
  classical
  rw [b6_type1122_original_count_eq_window_layers]
  calc
    (∑ r : B6Type1122WindowIndex,
      b6Type1122LayerSquareSum (r.2.1.val-2*r.2.2.1.val)
        r.2.2.1.val r.2.2.2.val r.1.val.2) =
      ∑ r : B6Type1122WindowIndex,
        b6Type1122WindowTerm (r.2.1.val-2*r.2.2.1.val)
          r.2.2.1.val r.2.2.2.val r.1.val.2 := by
      exact Finset.sum_congr rfl (fun r _ =>
        (b6_type1122_window_term_eq_layer _ _ _ _ (b6_type1122_window_outer_guard r)).symm)
    _ = b6Type1122WindowCount := by
      simp only [B6Type1122WindowIndex,Fintype.sum_sigma,Fintype.sum_prod_type,
        b6Type1122WindowCount,b6Type1122WindowCatalogBlock,b6Type1122WindowMassBlock,
        b6Type1122WindowQBlock]
#print axioms Paper7MomentCounts.b6_type1122_original_count_eq_window_sum

theorem b6_type1122_coefficient_sum_eq_window_sum :
    b6Type1122CoefficientSum=b6Type1122WindowCount := by
  rw [← b6_type1122_original_count_eq_coefficient_sum,b6_type1122_original_count_eq_window_sum]
#print axioms Paper7MomentCounts.b6_type1122_coefficient_sum_eq_window_sum

theorem b6_type1122_compressed_sum_eq_window_sum :
    b6Type1122CompressedCountSum=b6Type1122WindowCount := by
  rw [← b6_type1122_original_count_eq_compressed_sum,b6_type1122_original_count_eq_window_sum]
#print axioms Paper7MomentCounts.b6_type1122_compressed_sum_eq_window_sum

end Paper7MomentCounts

namespace Paper7MomentCanonicalSix
open Paper7MomentCounts

theorem b6_reflection_zero_count_eq_window_sum :
    b6FixedCount (b6Reflection 0)=b6Type1122WindowCount := by
  rw [b6_reflection_zero_count_eq_original_type1122,b6_type1122_original_count_eq_window_sum]
#print axioms Paper7MomentCanonicalSix.b6_reflection_zero_count_eq_window_sum

end Paper7MomentCanonicalSix
