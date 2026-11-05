import Research.Backfill.Paper7.MomentB6Type1122LayerSum

/-! Uncompiled exact original reflection count as a low-dimensional symbolic
sum. The catalogue enters through its set of moments, so witnesses are not
counted. Do not evaluate the entire index by decide/native/enumeration. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

abbrev B6Type1122MomentIndex :=
  Fin 37 × Fin 19 × Fin 19 × ↥(b6FeatureCatalog.image Prod.snd)
#print axioms Paper7MomentCounts.B6Type1122MomentIndex

def b6Type1122MomentIndexOf
    (x : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}) : B6Type1122MomentIndex := by
  have hg := (b6_type1122_candB1_iff x.val).mp x.property
  have hq := b6_type1122_original_fibre_Q_le (b6Type1122CapacityOf x.val)
    (b6Type1122Total x.val.2) ⟨x.val,fun _ => rfl,rfl⟩
  have hw := hg.2.1
  change b6Type1122Total (b6Type1122CapacityOf x.val)+b6Type1122Total x.val.2 ≤ 36 at hw
  have hA : b6Type1122CapacityOf x.val 0+b6Type1122CapacityOf x.val 3 < 37 := by
    unfold b6Type1122Total at hw
    omega
  have hB : b6Type1122CapacityOf x.val 1+b6Type1122CapacityOf x.val 2 < 19 := by
    unfold b6Type1122Total at hw
    omega
  have hQ : b6Type1122Total x.val.2 < 19 := by omega
  have hM : theta (b6Type1122Row x.val) ∈ b6FeatureCatalog.image Prod.snd := by
    obtain ⟨sm,hsm,ht,_,_⟩ := hg.2.2
    exact Finset.mem_image.mpr ⟨sm,hsm,ht.trans (b6_type1122_row_features x.val).2.2.symm⟩
  exact (⟨_,hA⟩,⟨_,hB⟩,⟨_,hQ⟩,⟨_,hM⟩)
#print axioms Paper7MomentCounts.b6Type1122MomentIndexOf

theorem b6_type1122_moment_index_eq_iff
    (x : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}) (r : B6Type1122MomentIndex) :
    b6Type1122MomentIndexOf x=r ↔
      b6Type1122CapacityOf x.val 0+b6Type1122CapacityOf x.val 3=r.1.val ∧
      b6Type1122CapacityOf x.val 1+b6Type1122CapacityOf x.val 2=r.2.1.val ∧
      b6Type1122Total x.val.2=r.2.2.1.val ∧
      theta (b6Type1122Row x.val)=r.2.2.2.val := by
  constructor
  · intro h
    exact ⟨congrArg (fun y : B6Type1122MomentIndex => y.1.val) h,
      congrArg (fun y : B6Type1122MomentIndex => y.2.1.val) h,
      congrArg (fun y : B6Type1122MomentIndex => y.2.2.1.val) h,
      congrArg (fun y : B6Type1122MomentIndex => y.2.2.2.val) h⟩
  · rintro ⟨hA,hB,hQ,hM⟩
    apply Prod.ext
    · exact Fin.ext hA
    · apply Prod.ext
      · exact Fin.ext hB
      · exact Prod.ext (Fin.ext hQ) (Subtype.ext hM)
#print axioms Paper7MomentCounts.b6_type1122_moment_index_eq_iff

def b6Type1122MomentLayerEquiv (r : B6Type1122MomentIndex) :
    {x : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} // b6Type1122MomentIndexOf x=r} ≃
      B6Type1122Layer r.1.val r.2.1.val r.2.2.1.val r.2.2.2.val where
  toFun x := by
    have h := (b6_type1122_moment_index_eq_iff x.val r).mp x.property
    exact ⟨x.val.val,h.1,h.2.1,h.2.2.1,h.2.2.2,x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2.2.2.2⟩,
    (b6_type1122_moment_index_eq_iff ⟨x.val,x.property.2.2.2.2⟩ r).mpr
      ⟨x.property.1,x.property.2.1,x.property.2.2.1,x.property.2.2.2.1⟩⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
#print axioms Paper7MomentCounts.b6Type1122MomentLayerEquiv

/-- Symbolic interface only: all outer guards remain in each layer. -/
def b6Type1122CompressedCountSum : ℕ :=
  ∑ r : B6Type1122MomentIndex,
    b6Type1122LayerSquareSum r.1.val r.2.1.val r.2.2.1.val r.2.2.2.val
#print axioms Paper7MomentCounts.b6Type1122CompressedCountSum

theorem b6_type1122_original_count_eq_compressed_sum :
    Nat.card {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}=b6Type1122CompressedCountSum := by
  let e := (Equiv.sigmaFiberEquiv b6Type1122MomentIndexOf).symm.trans
    (Equiv.sigmaCongrRight b6Type1122MomentLayerEquiv)
  rw [Nat.card_congr e,Nat.card_sigma]
  exact Finset.sum_congr rfl (fun r _ =>
    b6_type1122_layer_card_eq_square_sum r.1.val r.2.1.val r.2.2.1.val r.2.2.2.val)
#print axioms Paper7MomentCounts.b6_type1122_original_count_eq_compressed_sum

theorem b6_type1122_old_coefficient_sum_eq_compressed_sum :
    b6Type1122CoefficientSum=b6Type1122CompressedCountSum := by
  rw [← b6_type1122_original_count_eq_coefficient_sum,
    b6_type1122_original_count_eq_compressed_sum]
#print axioms Paper7MomentCounts.b6_type1122_old_coefficient_sum_eq_compressed_sum

theorem b6_type1122_moment_index_small_inner_bounds (r : B6Type1122MomentIndex) :
    Fintype.card (Fin (r.1.val+1)) ≤ 37 ∧
      Fintype.card (Fin (r.2.2.1.val/2+1)) ≤ 10 := by
  simp only [Fintype.card_fin]
  have hA := r.1.isLt
  have hQ := r.2.2.1.isLt
  omega
#print axioms Paper7MomentCounts.b6_type1122_moment_index_small_inner_bounds

end Paper7MomentCounts

namespace Paper7MomentCanonicalSix
open Paper7MomentCounts

theorem b6_reflection_zero_count_eq_compressed_sum :
    b6FixedCount (b6Reflection 0)=b6Type1122CompressedCountSum := by
  rw [b6_reflection_zero_count_eq_original_type1122,
    b6_type1122_original_count_eq_compressed_sum]
#print axioms Paper7MomentCanonicalSix.b6_reflection_zero_count_eq_compressed_sum

end Paper7MomentCanonicalSix
