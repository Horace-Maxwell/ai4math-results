import Research.Backfill.Paper7.MomentB6CatalogueConvolutionTotal
import Research.Backfill.Paper7.MomentB6Theta84Count
import Research.Backfill.Paper7.MomentB6Theta252Count
import Research.Backfill.Paper7.MomentB6TopMomentCount
import Research.Backfill.Paper7.MomentB6FourEmptyFibres

/-! Uncompiled candidate. Each complete catalogue convolution is transported
to the actual ordered original theta fibre. The three convolution ancestors
remain pending; the four imported numerical/empty-fibre modules are separately
bound to actual successful producers. No numerical convolution is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

abbrev B6ThetaCandidateFibre (T : ℤ) :=
  {x : PQ 6 // x ∈ CandB1 6 42 ∧ theta x = T}
#print axioms Paper7MomentCounts.B6ThetaCandidateFibre

def b6ThetaCandidateIndex (T : ℤ) (x : B6ThetaCandidateFibre T) : Fin 37 × Fin 19 :=
  (b6CandidateCatalogIndex ⟨x.val,x.property.1⟩).2
#print axioms Paper7MomentCounts.b6ThetaCandidateIndex

theorem b6ThetaCandidateIndex_eq_iff (T : ℤ) (x : B6ThetaCandidateFibre T)
    (r : Fin 37 × Fin 19) : b6ThetaCandidateIndex T x = r ↔
      (∑ i, (x.val.1 i+x.val.2 i)) = r.1.val ∧ qSum x.val = r.2.val := by
  constructor
  · intro h
    exact ⟨congrArg (fun a : Fin 37 × Fin 19 => a.1.val) h,
      congrArg (fun a : Fin 37 × Fin 19 => a.2.val) h⟩
  · rintro ⟨hz,hq⟩
    exact Prod.ext (Fin.ext hz) (Fin.ext hq)
#print axioms Paper7MomentCounts.b6ThetaCandidateIndex_eq_iff

def b6ThetaCandidateIndexFibreEquiv (sm : ↥b6FeatureCatalog) (r : Fin 37 × Fin 19) :
    {x : B6ThetaCandidateFibre sm.val.2 // b6ThetaCandidateIndex sm.val.2 x = r} ≃
      B6OriginalCatalogFibre (sm,r) where
  toFun x := ⟨x.val.val,
    ((b6ThetaCandidateIndex_eq_iff sm.val.2 x.val r).mp x.property).1,
    ((b6ThetaCandidateIndex_eq_iff sm.val.2 x.val r).mp x.property).2,
    x.val.property.2,x.val.property.1⟩
  invFun x := ⟨⟨x.val,x.property.2.2.2,x.property.2.2.1⟩,
    (b6ThetaCandidateIndex_eq_iff sm.val.2
      ⟨x.val,x.property.2.2.2,x.property.2.2.1⟩ r).mpr
        ⟨x.property.1,x.property.2.1⟩⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
#print axioms Paper7MomentCounts.b6ThetaCandidateIndexFibreEquiv

def b6ThetaCandidatePartitionEquiv (sm : ↥b6FeatureCatalog) :
    B6ThetaCandidateFibre sm.val.2 ≃
      Σ r : Fin 37 × Fin 19, B6OriginalCatalogFibre (sm,r) :=
  (Equiv.sigmaFiberEquiv (b6ThetaCandidateIndex sm.val.2)).symm.trans
    (Equiv.sigmaCongrRight (b6ThetaCandidateIndexFibreEquiv sm))
#print axioms Paper7MomentCounts.b6ThetaCandidatePartitionEquiv

theorem b6_theta_ncard_eq_catalog_statistic_sum (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard =
      ∑ Z ∈ Finset.range 37, ∑ Q ∈ Finset.range 19,
        if b6CatalogStatisticAccept sm Z Q then
          labelledExactCapacityQCard 6 Z (b6CatalogResidual sm Z Q) Q else 0 := by
  change Nat.card (B6ThetaCandidateFibre sm.2) = _
  rw [Nat.card_congr (b6ThetaCandidatePartitionEquiv ⟨sm,hsm⟩), Nat.card_sigma]
  simp only [Fintype.sum_prod_type, b6OriginalCatalogFibre_card]
  rw [Fin.sum_univ_eq_sum_range (fun Z : ℕ => ∑ q : Fin 19,
    if b6CatalogStatisticAccept sm Z q.val then
      labelledExactCapacityQCard 6 Z (b6CatalogResidual sm Z q.val) q.val else 0) 37]
  apply Finset.sum_congr rfl
  intro Z _hZ
  exact Fin.sum_univ_eq_sum_range (fun Q : ℕ =>
    if b6CatalogStatisticAccept sm Z Q then
      labelledExactCapacityQCard 6 Z (b6CatalogResidual sm Z Q) Q else 0) 19
#print axioms Paper7MomentCounts.b6_theta_ncard_eq_catalog_statistic_sum

def b6CatalogConvolutionTotal (sm : ℤ × ℤ) : ℤ :=
  ∑ Q ∈ Finset.range 19, b6CatalogConvolutionQSlice sm Q
#print axioms Paper7MomentCounts.b6CatalogConvolutionTotal

theorem b6CatalogConvolutionTotal_eq_theta_ncard (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    b6CatalogConvolutionTotal sm =
      ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  calc
    b6CatalogConvolutionTotal sm =
        ∑ Q ∈ Finset.range 19, ∑ Z ∈ Finset.range 37, b6CatalogConvolutionBlock sm Z Q := by
      apply Finset.sum_congr rfl
      intro Q _hQ
      exact (b6CatalogConvolutionBlock_sum_ZRange sm Q).symm
    _ = ∑ Z ∈ Finset.range 37, ∑ Q ∈ Finset.range 19,
        b6CatalogConvolutionBlock sm Z Q := Finset.sum_comm
    _ = ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
      rw [b6_theta_ncard_eq_catalog_statistic_sum sm hsm]
      simp only [Nat.cast_sum, b6CatalogConvolutionBlock_eq_actual]
#print axioms Paper7MomentCounts.b6CatalogConvolutionTotal_eq_theta_ncard

theorem b6_candD2_theta_fibre_eq_candB1 (T : ℤ) :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = T} =
      {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = T} := by
  ext x
  exact and_congr ((b6_candD2_iff_guard x).trans (b6_candB1_iff_guard x).symm) Iff.rfl
#print axioms Paper7MomentCounts.b6_candD2_theta_fibre_eq_candB1

theorem b6CatalogConvolutionTotal_eq_theta_ncard_D2 (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    b6CatalogConvolutionTotal sm =
      ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6_candD2_theta_fibre_eq_candB1]
  exact b6CatalogConvolutionTotal_eq_theta_ncard sm hsm
#print axioms Paper7MomentCounts.b6CatalogConvolutionTotal_eq_theta_ncard_D2

theorem b6CatalogConvolutionBlock_nonneg (sm : ℤ × ℤ) (Z Q : ℕ) :
    0 ≤ b6CatalogConvolutionBlock sm Z Q := by
  rw [b6CatalogConvolutionBlock_eq_actual]
  exact Int.natCast_nonneg _
#print axioms Paper7MomentCounts.b6CatalogConvolutionBlock_nonneg

theorem b6CatalogConvolutionQSlice_nonneg (sm : ℤ × ℤ) (Q : ℕ) :
    0 ≤ b6CatalogConvolutionQSlice sm Q :=
  Finset.sum_nonneg (fun Z _hZ => b6CatalogConvolutionBlock_nonneg sm Z Q)
#print axioms Paper7MomentCounts.b6CatalogConvolutionQSlice_nonneg

theorem b6CatalogConvolutionBlock_zero_of_Q_gt (sm : ℤ × ℤ) (Z Q : ℕ) (hQ : 18 < Q) :
    b6CatalogConvolutionBlock sm Z Q = 0 := by
  have hn : ¬ b6CatalogStatisticAccept sm Z Q := by
    intro ha
    have hb := ha.2.1
    have hq := ha.2.2.1
    omega
  exact ite_eq_right hn
#print axioms Paper7MomentCounts.b6CatalogConvolutionBlock_zero_of_Q_gt

theorem b6CatalogConvolutionQSlice_zero_of_Q_gt (sm : ℤ × ℤ) (Q : ℕ) (hQ : 18 < Q) :
    b6CatalogConvolutionQSlice sm Q = 0 := by
  apply Finset.sum_eq_zero
  intro Z _hZ
  exact b6CatalogConvolutionBlock_zero_of_Q_gt sm Z Q hQ
#print axioms Paper7MomentCounts.b6CatalogConvolutionQSlice_zero_of_Q_gt

theorem b6CatalogConvolutionQSlice_zero_of_total_zero (sm : ℤ × ℤ)
    (hzero : b6CatalogConvolutionTotal sm = 0) (Q : ℕ) :
    b6CatalogConvolutionQSlice sm Q = 0 := by
  by_cases hQ : Q ≤ 18
  · have hle : b6CatalogConvolutionQSlice sm Q ≤ b6CatalogConvolutionTotal sm :=
      Finset.single_le_sum (fun q _hq => b6CatalogConvolutionQSlice_nonneg sm q)
        (Finset.mem_range.mpr (by omega))
    exact le_antisymm (hzero ▸ hle) (b6CatalogConvolutionQSlice_nonneg sm Q)
  · exact b6CatalogConvolutionQSlice_zero_of_Q_gt sm Q (by omega)
#print axioms Paper7MomentCounts.b6CatalogConvolutionQSlice_zero_of_total_zero

theorem b6CatalogConvolutionBlock_zero_of_QSlice_zero (sm : ℤ × ℤ) (Q : ℕ)
    (hzero : b6CatalogConvolutionQSlice sm Q = 0) (Z : ℕ) :
    b6CatalogConvolutionBlock sm Z Q = 0 := by
  by_cases hZ : Z ∈ b6CatalogZRange sm Q
  · have hle : b6CatalogConvolutionBlock sm Z Q ≤ b6CatalogConvolutionQSlice sm Q :=
      Finset.single_le_sum (fun z _hz => b6CatalogConvolutionBlock_nonneg sm z Q) hZ
    exact le_antisymm (hzero ▸ hle) (b6CatalogConvolutionBlock_nonneg sm Z Q)
  · exact b6CatalogConvolutionBlock_zero_outside_ZRange sm Z Q hZ
#print axioms Paper7MomentCounts.b6CatalogConvolutionBlock_zero_of_QSlice_zero

theorem b6CatalogConvolutionTotal_excluded (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog)
    (hT : sm.2 ∈ b6ExcludedTheta) : b6CatalogConvolutionTotal sm = 0 := by
  rw [b6CatalogConvolutionTotal_eq_theta_ncard sm hsm,
    b6_candB1_excluded_theta_ncard sm.2 hT, Nat.cast_zero]
#print axioms Paper7MomentCounts.b6CatalogConvolutionTotal_excluded

theorem b6CatalogConvolutionBlock_excluded (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog)
    (hT : sm.2 ∈ b6ExcludedTheta) (Z Q : ℕ) : b6CatalogConvolutionBlock sm Z Q = 0 := by
  exact b6CatalogConvolutionBlock_zero_of_QSlice_zero sm Q
    (b6CatalogConvolutionQSlice_zero_of_total_zero sm
      (b6CatalogConvolutionTotal_excluded sm hsm hT) Q) Z
#print axioms Paper7MomentCounts.b6CatalogConvolutionBlock_excluded

theorem b6CatalogConvolutionTotal_theta84 : b6CatalogConvolutionTotal (13,84) = 66 := by
  have hm : (13,84) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h := b6CatalogConvolutionTotal_eq_theta_ncard (13,84) hm
  change b6CatalogConvolutionTotal (13,84) =
    ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 84}.ncard : ℤ) at h
  rw [b6_theta84_candB1_ncard] at h
  exact h
#print axioms Paper7MomentCounts.b6CatalogConvolutionTotal_theta84

theorem b6CatalogConvolutionTotal_theta252 : b6CatalogConvolutionTotal (20,252) = 36 := by
  have hm : (20,252) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h := b6CatalogConvolutionTotal_eq_theta_ncard (20,252) hm
  change b6CatalogConvolutionTotal (20,252) =
    ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 252}.ncard : ℤ) at h
  rw [b6_theta252_candB1_ncard] at h
  exact h
#print axioms Paper7MomentCounts.b6CatalogConvolutionTotal_theta252

theorem b6CatalogConvolutionTotal_theta1272 : b6CatalogConvolutionTotal (40,1272) = 6 := by
  have hm : (40,1272) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h := b6CatalogConvolutionTotal_eq_theta_ncard (40,1272) hm
  change b6CatalogConvolutionTotal (40,1272) =
    ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 1272}.ncard : ℤ) at h
  rw [b6_top_moment_candB1_ncard] at h
  exact h
#print axioms Paper7MomentCounts.b6CatalogConvolutionTotal_theta1272

end Paper7MomentCounts
