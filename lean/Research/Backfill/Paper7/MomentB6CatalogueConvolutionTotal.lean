import Research.Backfill.Paper7.MomentB6OriginalPQTripleConvolutionV2
import Research.Backfill.Paper7.MomentB6FeatureGuard

/-! Uncompiled candidate: exhaustive original21-catalogue labelled count.
The original-PQ and six-triple sources are pending parents, not successful objects.
The successful original feature-catalogue guard is used as an existential predicate;
feature witnesses are not counted. No target value or coverage premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

theorem b6FeatureCatalog_theta_injective :
    Set.InjOn Prod.snd (↑b6FeatureCatalog : Set (ℤ × ℤ)) := by
  intro p hp q hq h
  have hpS := (b6FeatureCatalog_witness p.1 p.2 hp).2.1
  have hqS := (b6FeatureCatalog_witness q.1 q.2 hq).2.1
  rw [h] at hpS
  exact Prod.ext (hpS.symm.trans hqS) h
#print axioms Paper7MomentCounts.b6FeatureCatalog_theta_injective

def b6OriginalPQStatRow (x : PQ 6) :
    labelledOriginalPQStatisticFibre 6
      (∑ i, (x.1 i+x.2 i)) (∑ i, (x.1 i+x.2 i)^2) (qSum x) :=
  ⟨x,rfl,rfl,rfl⟩
#print axioms Paper7MomentCounts.b6OriginalPQStatRow

theorem labelledCapacityQFibre_cauchy (n A B Q : ℕ)
    (x : labelledCapacityQFibre n A B Q) : A^2 ≤ n*B := by
  have ha : (∑ i, (x.val.1 i : ℤ)) = A := by exact_mod_cast x.property.2.1
  have hb : (∑ i, (x.val.1 i : ℤ)^2) = B := by exact_mod_cast x.property.2.2.1
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => (x.val.1 i : ℤ))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [ha,hb] at h
  exact_mod_cast h
#print axioms Paper7MomentCounts.labelledCapacityQFibre_cauchy

def b6CatalogResidual (sm : ℤ × ℤ) (Z Q : ℕ) : ℕ :=
  (sm.2 - 12 - 3*(Z : ℤ) - 2*(Q : ℤ)).toNat
#print axioms Paper7MomentCounts.b6CatalogResidual

def b6CatalogStatisticAccept (sm : ℤ × ℤ) (Z Q : ℕ) : Prop :=
  0 < Z+Q ∧ Z+Q ≤ 36 ∧ Q ≤ Z ∧
    0 ≤ sm.2 - 12 - 3*(Z : ℤ) - 2*(Q : ℤ) ∧
    b6CatalogResidual sm Z Q ≤ Z^2 ∧ Z^2 ≤ 6*b6CatalogResidual sm Z Q ∧
    sm.1 ≤ (6+(Z+Q : ℕ) : ℤ) ∧
    (6+(Z+Q : ℕ) : ℤ) - max (Q : ℤ) 2 ≤ sm.1
#print axioms Paper7MomentCounts.b6CatalogStatisticAccept

abbrev B6CatalogStatisticIndex := ↥b6FeatureCatalog × Fin 37 × Fin 19
#print axioms Paper7MomentCounts.B6CatalogStatisticIndex

def b6CandidateSpectralEntry (x : {x : PQ 6 // x ∈ CandB1 6 42}) : ↥b6FeatureCatalog :=
  ⟨Classical.choose (((b6_candB1_iff_guard x.val).mp x.property).2.2),
    (Classical.choose_spec (((b6_candB1_iff_guard x.val).mp x.property).2.2)).1⟩
#print axioms Paper7MomentCounts.b6CandidateSpectralEntry

theorem b6CandidateSpectralEntry_theta (x : {x : PQ 6 // x ∈ CandB1 6 42}) :
    (b6CandidateSpectralEntry x).val.2 = theta x.val :=
  (Classical.choose_spec (((b6_candB1_iff_guard x.val).mp x.property).2.2)).2.1
#print axioms Paper7MomentCounts.b6CandidateSpectralEntry_theta

def b6CandidateCatalogIndex (x : {x : PQ 6 // x ∈ CandB1 6 42}) : B6CatalogStatisticIndex :=
  let h := labelledOriginalPQStatistic_six_budget_bounds _ _ _ (b6OriginalPQStatRow x.val) x.property.1
  (b6CandidateSpectralEntry x,
   ⟨∑ i, (x.val.1 i+x.val.2 i), by omega⟩,
   ⟨qSum x.val, by omega⟩)
#print axioms Paper7MomentCounts.b6CandidateCatalogIndex

theorem b6CandidateCatalogIndex_eq_iff (x : {x : PQ 6 // x ∈ CandB1 6 42})
    (r : B6CatalogStatisticIndex) : b6CandidateCatalogIndex x = r ↔
      (∑ i, (x.val.1 i+x.val.2 i)) = r.2.1.val ∧
        qSum x.val = r.2.2.val ∧ theta x.val = r.1.val.2 := by
  constructor
  · intro h
    refine ⟨congrArg (fun a : B6CatalogStatisticIndex => a.2.1.val) h,
      congrArg (fun a : B6CatalogStatisticIndex => a.2.2.val) h, ?_⟩
    exact (b6CandidateSpectralEntry_theta x).symm.trans
      (congrArg (fun a : B6CatalogStatisticIndex => a.1.val.2) h)
  · rintro ⟨hz,hq,ht⟩
    apply Prod.ext
    · apply Subtype.ext
      apply b6FeatureCatalog_theta_injective (b6CandidateSpectralEntry x).property r.1.property
      exact (b6CandidateSpectralEntry_theta x).trans ht
    · exact Prod.ext (Fin.ext hz) (Fin.ext hq)
#print axioms Paper7MomentCounts.b6CandidateCatalogIndex_eq_iff

abbrev B6OriginalCatalogFibre (r : B6CatalogStatisticIndex) :=
  {x : PQ 6 // (∑ i, (x.1 i+x.2 i)) = r.2.1.val ∧ qSum x = r.2.2.val ∧
    theta x = r.1.val.2 ∧ x ∈ CandB1 6 42}
#print axioms Paper7MomentCounts.B6OriginalCatalogFibre

def b6CandidateCatalogIndexFibreEquiv (r : B6CatalogStatisticIndex) :
    {x : {x : PQ 6 // x ∈ CandB1 6 42} // b6CandidateCatalogIndex x = r} ≃
      B6OriginalCatalogFibre r where
  toFun x := ⟨x.val.val, ((b6CandidateCatalogIndex_eq_iff x.val r).mp x.property).1,
    ((b6CandidateCatalogIndex_eq_iff x.val r).mp x.property).2.1,
    ((b6CandidateCatalogIndex_eq_iff x.val r).mp x.property).2.2, x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2.2.2⟩,
    (b6CandidateCatalogIndex_eq_iff ⟨x.val,x.property.2.2.2⟩ r).mpr
      ⟨x.property.1,x.property.2.1,x.property.2.2.1⟩⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
#print axioms Paper7MomentCounts.b6CandidateCatalogIndexFibreEquiv

instance b6OriginalCatalogFibreFinite (r : B6CatalogStatisticIndex) :
    Finite (B6OriginalCatalogFibre r) := by
  let : Finite {x : PQ 6 // x ∈ CandB1 6 42} := candB1_finite 6 42
  apply Finite.of_injective
    (fun x : B6OriginalCatalogFibre r =>
      (⟨x.val,x.property.2.2.2⟩ : {x : PQ 6 // x ∈ CandB1 6 42}))
  intro x y h
  apply Subtype.ext
  exact congrArg (fun x : {x : PQ 6 // x ∈ CandB1 6 42} => x.val) h
#print axioms Paper7MomentCounts.b6OriginalCatalogFibreFinite

def b6CandidateCatalogPartitionEquiv :
    {x : PQ 6 // x ∈ CandB1 6 42} ≃ Σ r : B6CatalogStatisticIndex, B6OriginalCatalogFibre r :=
  (Equiv.sigmaFiberEquiv b6CandidateCatalogIndex).symm.trans
    (Equiv.sigmaCongrRight b6CandidateCatalogIndexFibreEquiv)
#print axioms Paper7MomentCounts.b6CandidateCatalogPartitionEquiv

theorem b6OriginalCatalogFibre_residual (r : B6CatalogStatisticIndex)
    (x : B6OriginalCatalogFibre r) :
    b6CatalogResidual r.1.val r.2.1.val r.2.2.val = ∑ i, (x.val.1 i+x.val.2 i)^2 := by
  let y : labelledOriginalPQStatisticFibre 6 r.2.1.val
      (∑ i, (x.val.1 i+x.val.2 i)^2) r.2.2.val :=
    ⟨x.val,x.property.1,rfl,x.property.2.1⟩
  have ht := labelledOriginalPQStatistic_theta _ _ _ _ y
  have hm := x.property.2.2.1
  have he : r.1.val.2 - 12 - 3*(r.2.1.val : ℤ) - 2*(r.2.2.val : ℤ) =
      ((∑ i, (x.val.1 i+x.val.2 i)^2 : ℕ) : ℤ) := by
    change theta x.val = _ at ht
    omega
  unfold b6CatalogResidual
  rw [he, Int.toNat_natCast]
#print axioms Paper7MomentCounts.b6OriginalCatalogFibre_residual

theorem b6OriginalCatalogFibre_accept (r : B6CatalogStatisticIndex)
    (x : B6OriginalCatalogFibre r) :
    b6CatalogStatisticAccept r.1.val r.2.1.val r.2.2.val := by
  let y : labelledOriginalPQStatisticFibre 6 r.2.1.val
      (b6CatalogResidual r.1.val r.2.1.val r.2.2.val) r.2.2.val :=
    ⟨x.val,x.property.1,(b6OriginalCatalogFibre_residual r x).symm,x.property.2.1⟩
  have hb := labelledOriginalPQStatistic_six_budget_bounds _ _ _ y x.property.2.2.2.1
  have hc := labelledCapacityQFibre_cauchy 6 _ _ _ (labelledOriginalPQStatisticEquiv _ _ _ _ y)
  have ht := labelledOriginalPQStatistic_theta _ _ _ _ y
  have hm := x.property.2.2.1
  have hn : 0 ≤ r.1.val.2 - 12 - 3*(r.2.1.val : ℤ) - 2*(r.2.2.val : ℤ) := by
    have hnon := Int.natCast_nonneg (b6CatalogResidual r.1.val r.2.1.val r.2.2.val)
    change theta x.val = _ at ht
    omega
  have hg := ((b6_candB1_iff_guard x.val).mp x.property.2.2.2).2.2
  obtain ⟨sm,hsm,hsmT,hu,hl⟩ := hg
  have he : sm = r.1.val := b6FeatureCatalog_theta_injective hsm r.1.property (hsmT.trans hm)
  subst sm
  rw [labelledOriginalPQStatistic_weight _ _ _ _ y] at hu hl
  rw [x.property.2.1] at hl
  exact ⟨hb.1,hb.2.1,hb.2.2.1,hn,hb.2.2.2.2.2,hc,hu,hl⟩
#print axioms Paper7MomentCounts.b6OriginalCatalogFibre_accept

def b6OriginalCatalogFibreEquivStatistics (r : B6CatalogStatisticIndex)
    (ha : b6CatalogStatisticAccept r.1.val r.2.1.val r.2.2.val) :
    B6OriginalCatalogFibre r ≃ labelledOriginalPQStatisticFibre 6 r.2.1.val
      (b6CatalogResidual r.1.val r.2.1.val r.2.2.val) r.2.2.val where
  toFun x := ⟨x.val,x.property.1,(b6OriginalCatalogFibre_residual r x).symm,x.property.2.1⟩
  invFun y := ⟨y.val, by
    rcases ha with ⟨hpos,hbudget,_hq,hn,_hupper,_hlower,hu,hl⟩
    have hres : (b6CatalogResidual r.1.val r.2.1.val r.2.2.val : ℤ) =
        r.1.val.2 - 12 - 3*(r.2.1.val : ℤ) - 2*(r.2.2.val : ℤ) :=
      Int.toNat_of_nonneg hn
    have ht : theta y.val = r.1.val.2 := by
      have h := labelledOriginalPQStatistic_theta _ _ _ _ y
      omega
    have hmem : y.val ∈ CandB1 6 42 := by
      apply (b6_candB1_iff_guard y.val).mpr
      unfold b6CandidateGuard
      rw [labelledOriginalPQStatistic_weight _ _ _ _ y, y.property.2.2, ht]
      exact ⟨hpos,hbudget,⟨r.1.val,r.1.property,rfl,hu,hl⟩⟩
    exact ⟨y.property.1,y.property.2.2,ht,hmem⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl
#print axioms Paper7MomentCounts.b6OriginalCatalogFibreEquivStatistics

theorem b6OriginalCatalogFibre_card (r : B6CatalogStatisticIndex) :
    Nat.card (B6OriginalCatalogFibre r) =
      if b6CatalogStatisticAccept r.1.val r.2.1.val r.2.2.val then
        labelledExactCapacityQCard 6 r.2.1.val
          (b6CatalogResidual r.1.val r.2.1.val r.2.2.val) r.2.2.val else 0 := by
  by_cases ha : b6CatalogStatisticAccept r.1.val r.2.1.val r.2.2.val
  · rw [ite_eq_left ha]
    exact (Nat.card_congr (b6OriginalCatalogFibreEquivStatistics r ha)).trans
      (labelledOriginalPQStatisticFibre_card _ _ _ _)
  · let : IsEmpty (B6OriginalCatalogFibre r) := ⟨fun x => ha (b6OriginalCatalogFibre_accept r x)⟩
    rw [ite_eq_right ha, Nat.card_of_isEmpty]
#print axioms Paper7MomentCounts.b6OriginalCatalogFibre_card

theorem b6_candB1_ncard_eq_catalog_statistic_fibres :
    (CandB1 6 42).ncard =
      ∑ r : B6CatalogStatisticIndex,
        if b6CatalogStatisticAccept r.1.val r.2.1.val r.2.2.val then
          labelledExactCapacityQCard 6 r.2.1.val
            (b6CatalogResidual r.1.val r.2.1.val r.2.2.val) r.2.2.val else 0 := by
  change Nat.card {x : PQ 6 // x ∈ CandB1 6 42} = _
  rw [Nat.card_congr b6CandidateCatalogPartitionEquiv, Nat.card_sigma]
  exact Finset.sum_congr rfl (fun r _hr => b6OriginalCatalogFibre_card r)
#print axioms Paper7MomentCounts.b6_candB1_ncard_eq_catalog_statistic_fibres

theorem b6_candB1_ncard_eq_catalog_statistic_sum :
    (CandB1 6 42).ncard =
      ∑ sm ∈ b6FeatureCatalog, ∑ Z ∈ Finset.range 37, ∑ Q ∈ Finset.range 19,
        if b6CatalogStatisticAccept sm Z Q then
          labelledExactCapacityQCard 6 Z (b6CatalogResidual sm Z Q) Q else 0 := by
  rw [b6_candB1_ncard_eq_catalog_statistic_fibres]
  simp only [Fintype.sum_prod_type]
  calc
    (∑ sm : ↥b6FeatureCatalog, ∑ z : Fin 37, ∑ q : Fin 19,
      if b6CatalogStatisticAccept sm.val z.val q.val then
        labelledExactCapacityQCard 6 z.val (b6CatalogResidual sm.val z.val q.val) q.val else 0) =
        ∑ sm : ↥b6FeatureCatalog, ∑ Z ∈ Finset.range 37, ∑ Q ∈ Finset.range 19,
          if b6CatalogStatisticAccept sm.val Z Q then
            labelledExactCapacityQCard 6 Z (b6CatalogResidual sm.val Z Q) Q else 0 := by
      apply Finset.sum_congr rfl
      intro sm _hsm
      rw [Fin.sum_univ_eq_sum_range (fun Z : ℕ => ∑ q : Fin 19,
        if b6CatalogStatisticAccept sm.val Z q.val then
          labelledExactCapacityQCard 6 Z (b6CatalogResidual sm.val Z q.val) q.val else 0) 37]
      apply Finset.sum_congr rfl
      intro Z _hZ
      exact Fin.sum_univ_eq_sum_range (fun Q : ℕ =>
        if b6CatalogStatisticAccept sm.val Z Q then
          labelledExactCapacityQCard 6 Z (b6CatalogResidual sm.val Z Q) Q else 0) 19
    _ = ∑ sm ∈ b6FeatureCatalog, ∑ Z ∈ Finset.range 37, ∑ Q ∈ Finset.range 19,
        if b6CatalogStatisticAccept sm Z Q then
          labelledExactCapacityQCard 6 Z (b6CatalogResidual sm Z Q) Q else 0 :=
      Finset.sum_coe_sort b6FeatureCatalog (fun sm : ℤ × ℤ =>
        ∑ Z ∈ Finset.range 37, ∑ Q ∈ Finset.range 19,
          if b6CatalogStatisticAccept sm Z Q then
            labelledExactCapacityQCard 6 Z (b6CatalogResidual sm Z Q) Q else 0)
#print axioms Paper7MomentCounts.b6_candB1_ncard_eq_catalog_statistic_sum

def b6CatalogConvolutionBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  if b6CatalogStatisticAccept sm Z Q then
    ∑ A ∈ Finset.range (Z+1), ∑ B ∈ Finset.range (b6CatalogResidual sm Z Q+1),
      if B6TripleStatisticGuard A B ∧
          B6TripleStatisticGuard (Z-A) (b6CatalogResidual sm Z Q-B) then
        ∑ t ∈ labelledTripleQSplitRange Z A Q,
          labelledTripleDiscriminantKernel A B t *
            labelledTripleDiscriminantKernel (Z-A) (b6CatalogResidual sm Z Q-B) (Q-t)
      else 0
  else 0
#print axioms Paper7MomentCounts.b6CatalogConvolutionBlock

theorem b6CatalogConvolutionBlock_eq_actual (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6CatalogConvolutionBlock sm Z Q =
      ((if b6CatalogStatisticAccept sm Z Q then
        labelledExactCapacityQCard 6 Z (b6CatalogResidual sm Z Q) Q else 0 : ℕ) : ℤ) := by
  unfold b6CatalogConvolutionBlock
  by_cases ha : b6CatalogStatisticAccept sm Z Q
  · rw [ite_eq_left ha, ite_eq_left ha]
    exact (labelledExactCapacityQCard_six_kernel_statistic_pruned Z (b6CatalogResidual sm Z Q) Q).symm
  · rw [ite_eq_right ha, ite_eq_right ha, Nat.cast_zero]
#print axioms Paper7MomentCounts.b6CatalogConvolutionBlock_eq_actual

theorem b6_candB1_ncard_eq_catalog_convolution :
    ((CandB1 6 42).ncard : ℤ) =
      ∑ sm ∈ b6FeatureCatalog, ∑ Z ∈ Finset.range 37, ∑ Q ∈ Finset.range 19,
        b6CatalogConvolutionBlock sm Z Q := by
  rw [b6_candB1_ncard_eq_catalog_statistic_sum]
  simp only [Nat.cast_sum, b6CatalogConvolutionBlock_eq_actual]
#print axioms Paper7MomentCounts.b6_candB1_ncard_eq_catalog_convolution

theorem b6_candD2_ncard_eq_catalog_convolution :
    ((CandD2 6 42).ncard : ℤ) =
      ∑ sm ∈ b6FeatureCatalog, ∑ Z ∈ Finset.range 37, ∑ Q ∈ Finset.range 19,
        b6CatalogConvolutionBlock sm Z Q := by
  rw [candD2_ncard_eq_candB1_of_even 6 42 (show Even (6 : ℕ) from ⟨3,rfl⟩)]
  exact b6_candB1_ncard_eq_catalog_convolution
#print axioms Paper7MomentCounts.b6_candD2_ncard_eq_catalog_convolution

theorem b6CatalogStatisticAccept_spectral_window (sm : ℤ × ℤ) (Z Q : ℕ)
    (h : b6CatalogStatisticAccept sm Z Q) :
    sm.1-6-(Q : ℤ) ≤ (Z : ℤ) ∧
      (Z : ℤ) ≤ sm.1-6-(Q : ℤ)+max (Q : ℤ) 2 := by
  rcases h with ⟨_hpos,_hbudget,_hq,_hn,_hupper,_hlower,hu,hl⟩
  omega
#print axioms Paper7MomentCounts.b6CatalogStatisticAccept_spectral_window

theorem b6CatalogStatisticAccept_window_Qzero (sm : ℤ × ℤ) (Z : ℕ)
    (h : b6CatalogStatisticAccept sm Z 0) : sm.1-6 ≤ (Z : ℤ) ∧ (Z : ℤ) ≤ sm.1-4 := by
  have hw := b6CatalogStatisticAccept_spectral_window sm Z 0 h
  norm_num at hw
  omega
#print axioms Paper7MomentCounts.b6CatalogStatisticAccept_window_Qzero

theorem b6CatalogStatisticAccept_window_Qone (sm : ℤ × ℤ) (Z : ℕ)
    (h : b6CatalogStatisticAccept sm Z 1) : sm.1-7 ≤ (Z : ℤ) ∧ (Z : ℤ) ≤ sm.1-5 := by
  have hw := b6CatalogStatisticAccept_spectral_window sm Z 1 h
  norm_num at hw
  omega
#print axioms Paper7MomentCounts.b6CatalogStatisticAccept_window_Qone

theorem b6CatalogStatisticAccept_window_Qlarge (sm : ℤ × ℤ) (Z Q : ℕ)
    (hQ : 2 ≤ Q) (h : b6CatalogStatisticAccept sm Z Q) :
    sm.1-6-(Q : ℤ) ≤ (Z : ℤ) ∧ (Z : ℤ) ≤ sm.1-6 := by
  have hw := b6CatalogStatisticAccept_spectral_window sm Z Q h
  rw [max_eq_left (show (2 : ℤ) ≤ (Q : ℤ) by exact_mod_cast hQ)] at hw
  omega
#print axioms Paper7MomentCounts.b6CatalogStatisticAccept_window_Qlarge

theorem b6CatalogStatisticAccept_quadratic_bound (sm : ℤ × ℤ) (Z Q : ℕ)
    (h : b6CatalogStatisticAccept sm Z Q) :
    ((Z : ℤ)+9)^2+12*(Q : ℤ) ≤ 6*sm.2+9 := by
  rcases h with ⟨_hpos,_hbudget,_hq,hn,_hupper,hlower,_hu,_hl⟩
  have hr : (b6CatalogResidual sm Z Q : ℤ) = sm.2-12-3*(Z : ℤ)-2*(Q : ℤ) :=
    Int.toNat_of_nonneg hn
  have hc : (Z : ℤ)^2 ≤ 6*(b6CatalogResidual sm Z Q : ℤ) := by exact_mod_cast hlower
  nlinarith
#print axioms Paper7MomentCounts.b6CatalogStatisticAccept_quadratic_bound

def b6CatalogZRange (sm : ℤ × ℤ) (Q : ℕ) : Finset ℕ :=
  Finset.Icc (max Q (sm.1-6-(Q : ℤ)).toNat)
    (min (36-Q) (sm.1-6-(Q : ℤ)+max (Q : ℤ) 2).toNat)
#print axioms Paper7MomentCounts.b6CatalogZRange

theorem b6CatalogStatisticAccept_mem_ZRange (sm : ℤ × ℤ) (Z Q : ℕ)
    (h : b6CatalogStatisticAccept sm Z Q) : Z ∈ b6CatalogZRange sm Q := by
  have hw := b6CatalogStatisticAccept_spectral_window sm Z Q h
  have hlo : (sm.1-6-(Q : ℤ)).toNat ≤ Z := Int.toNat_le.mpr hw.1
  have hn : 0 ≤ sm.1-6-(Q : ℤ)+max (Q : ℤ) 2 := by omega
  have hup : Z ≤ (sm.1-6-(Q : ℤ)+max (Q : ℤ) 2).toNat := (Int.le_toNat hn).mpr hw.2
  have hb := h.2.1
  have hq := h.2.2.1
  apply Finset.mem_Icc.mpr
  exact ⟨max_le hq hlo,le_min (by omega) hup⟩
#print axioms Paper7MomentCounts.b6CatalogStatisticAccept_mem_ZRange

theorem b6CatalogConvolutionBlock_zero_outside_ZRange (sm : ℤ × ℤ) (Z Q : ℕ)
    (h : Z ∉ b6CatalogZRange sm Q) : b6CatalogConvolutionBlock sm Z Q = 0 := by
  have hn : ¬ b6CatalogStatisticAccept sm Z Q := fun ha => h (b6CatalogStatisticAccept_mem_ZRange sm Z Q ha)
  exact ite_eq_right hn
#print axioms Paper7MomentCounts.b6CatalogConvolutionBlock_zero_outside_ZRange

theorem b6CatalogConvolutionBlock_sum_ZRange (sm : ℤ × ℤ) (Q : ℕ) :
    (∑ Z ∈ Finset.range 37, b6CatalogConvolutionBlock sm Z Q) =
      ∑ Z ∈ b6CatalogZRange sm Q, b6CatalogConvolutionBlock sm Z Q := by
  symm
  apply Finset.sum_subset
  · intro Z hZ
    have hu := (Finset.mem_Icc.mp hZ).2
    apply Finset.mem_range.mpr
    omega
  · intro Z _hZ hn
    exact b6CatalogConvolutionBlock_zero_outside_ZRange sm Z Q hn
#print axioms Paper7MomentCounts.b6CatalogConvolutionBlock_sum_ZRange

def b6CatalogConvolutionQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  ∑ Z ∈ b6CatalogZRange sm Q, b6CatalogConvolutionBlock sm Z Q
#print axioms Paper7MomentCounts.b6CatalogConvolutionQSlice

theorem b6_candB1_ncard_eq_catalog_Qslices :
    ((CandB1 6 42).ncard : ℤ) =
      ∑ sm ∈ b6FeatureCatalog, ∑ Q ∈ Finset.range 19, b6CatalogConvolutionQSlice sm Q := by
  rw [b6_candB1_ncard_eq_catalog_convolution]
  apply Finset.sum_congr rfl
  intro sm _hsm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Q _hQ
  exact b6CatalogConvolutionBlock_sum_ZRange sm Q
#print axioms Paper7MomentCounts.b6_candB1_ncard_eq_catalog_Qslices

theorem b6_candD2_ncard_eq_catalog_Qslices :
    ((CandD2 6 42).ncard : ℤ) =
      ∑ sm ∈ b6FeatureCatalog, ∑ Q ∈ Finset.range 19, b6CatalogConvolutionQSlice sm Q := by
  rw [candD2_ncard_eq_candB1_of_even 6 42 (show Even (6 : ℕ) from ⟨3,rfl⟩)]
  exact b6_candB1_ncard_eq_catalog_Qslices
#print axioms Paper7MomentCounts.b6_candD2_ncard_eq_catalog_Qslices

end Paper7MomentCounts
