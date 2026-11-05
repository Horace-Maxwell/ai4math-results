import Research.Backfill.Paper7.MomentB6Type1122LoadWindow

/-! Pending exact partition by unique catalogue item, analytic mass window,
one pair sum and a load-dependent Q interval. No numerical sum is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

abbrev B6Type1122WindowIndex :=
  Σ sm : ↥b6FeatureCatalog,
    Σ Z : ↥(b6Type1122MassWindow sm.val.1 sm.val.2),
      Fin (Z.val/2+1) ×
        ↥(Finset.Icc (b6Type1122QLower (b6Type1122LoadCenter sm.val.1) Z.val)
          (b6Type1122QUpper (b6Type1122LoadCenter sm.val.1) Z.val))
#print axioms Paper7MomentCounts.B6Type1122WindowIndex

def b6Type1122WindowFields (r : B6Type1122WindowIndex) :
    (ℤ × ℤ) × ℕ × ℕ × ℕ :=
  (r.1.val,r.2.1.val,r.2.2.1.val,r.2.2.2.val)
#print axioms Paper7MomentCounts.b6Type1122WindowFields

theorem b6_type1122_window_fields_injective :
    Function.Injective b6Type1122WindowFields := by
  rintro ⟨sm,Z,B,Q⟩ ⟨sm',Z',B',Q'⟩ h
  change (sm.val,Z.val,B.val,Q.val)=(sm'.val,Z'.val,B'.val,Q'.val) at h
  have hsm : sm=sm' := Subtype.ext (congrArg Prod.fst h)
  subst sm'
  have hZ : Z=Z' := Subtype.ext (congrArg (fun x : (ℤ × ℤ) × ℕ × ℕ × ℕ => x.2.1) h)
  subst Z'
  have hB : B=B' := Fin.ext (congrArg (fun x : (ℤ × ℤ) × ℕ × ℕ × ℕ => x.2.2.1) h)
  have hQ : Q=Q' := Subtype.ext (congrArg (fun x : (ℤ × ℤ) × ℕ × ℕ × ℕ => x.2.2.2) h)
  subst B'
  subst Q'
  rfl
#print axioms Paper7MomentCounts.b6_type1122_window_fields_injective

def b6Type1122WindowIndexOf
    (x : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}) : B6Type1122WindowIndex := by
  let z := b6Type1122CapacityOf x.val
  let Q := b6Type1122Total x.val.2
  have hg : b6Type1122Guard z Q := (b6_type1122_candB1_iff x.val).mp x.property
  have hq : Q ≤ b6Type1122Total z :=
    b6_type1122_original_fibre_Q_le z Q ⟨x.val,fun _ => rfl,rfl⟩
  let sm := Classical.choose (b6_type1122_candidate_window z Q hg hq)
  have h := Classical.choose_spec (b6_type1122_candidate_window z Q hg hq)
  have hB : z 1+z 2 < b6Type1122Total z/2+1 := by
    unfold b6Type1122Total
    omega
  exact ⟨⟨sm,h.1⟩,⟨b6Type1122Total z,h.2.2.1⟩,⟨z 1+z 2,hB⟩,⟨Q,h.2.2.2⟩⟩
#print axioms Paper7MomentCounts.b6Type1122WindowIndexOf

theorem b6_type1122_window_index_features
    (x : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}) :
    (b6Type1122WindowIndexOf x).2.1.val=b6Type1122Total (b6Type1122CapacityOf x.val) ∧
    (b6Type1122WindowIndexOf x).2.2.1.val=
      b6Type1122CapacityOf x.val 1+b6Type1122CapacityOf x.val 2 ∧
    (b6Type1122WindowIndexOf x).2.2.2.val=b6Type1122Total x.val.2 ∧
    (b6Type1122WindowIndexOf x).1.val.2=theta (b6Type1122Row x.val) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  let z := b6Type1122CapacityOf x.val
  let Q := b6Type1122Total x.val.2
  have hg : b6Type1122Guard z Q := (b6_type1122_candB1_iff x.val).mp x.property
  have hq : Q ≤ b6Type1122Total z :=
    b6_type1122_original_fibre_Q_le z Q ⟨x.val,fun _ => rfl,rfl⟩
  have h := Classical.choose_spec (b6_type1122_candidate_window z Q hg hq)
  exact h.2.1.trans (b6_type1122_row_features x.val).2.2.symm
#print axioms Paper7MomentCounts.b6_type1122_window_index_features

theorem b6_type1122_window_index_eq_iff
    (x : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}) (r : B6Type1122WindowIndex) :
    b6Type1122WindowIndexOf x=r ↔
      b6Type1122Total (b6Type1122CapacityOf x.val)=r.2.1.val ∧
      b6Type1122CapacityOf x.val 1+b6Type1122CapacityOf x.val 2=r.2.2.1.val ∧
      b6Type1122Total x.val.2=r.2.2.2.val ∧
      theta (b6Type1122Row x.val)=r.1.val.2 := by
  have hf := b6_type1122_window_index_features x
  constructor
  · intro he
    rw [he] at hf
    exact ⟨hf.1.symm,hf.2.1.symm,hf.2.2.1.symm,hf.2.2.2.symm⟩
  · rintro ⟨hZ,hB,hQ,hM⟩
    have hsm : (b6Type1122WindowIndexOf x).1.val=r.1.val :=
      b6_type1122_catalog_moment_injective _ _
        (b6Type1122WindowIndexOf x).1.property r.1.property (hf.2.2.2.trans hM)
    apply b6_type1122_window_fields_injective
    exact Prod.ext hsm (Prod.ext (hf.1.trans hZ)
      (Prod.ext (hf.2.1.trans hB) (hf.2.2.1.trans hQ)))
#print axioms Paper7MomentCounts.b6_type1122_window_index_eq_iff

theorem b6_type1122_window_A_recovery (r : B6Type1122WindowIndex) :
    r.2.1.val-2*r.2.2.1.val+2*r.2.2.1.val=r.2.1.val := by
  have hB := r.2.2.1.isLt
  omega
#print axioms Paper7MomentCounts.b6_type1122_window_A_recovery

def b6Type1122WindowLayerEquiv (r : B6Type1122WindowIndex) :
    {x : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} // b6Type1122WindowIndexOf x=r} ≃
      B6Type1122Layer (r.2.1.val-2*r.2.2.1.val) r.2.2.1.val r.2.2.2.val r.1.val.2 where
  toFun x := by
    have h := (b6_type1122_window_index_eq_iff x.val r).mp x.property
    refine ⟨x.val.val,?_,h.2.1,h.2.2.1,h.2.2.2,x.val.property⟩
    have hZ := h.1
    have hpair := h.2.1
    unfold b6Type1122Total at hZ
    omega
  invFun x := by
    have hA := x.property.1
    have hB := x.property.2.1
    have hr := b6_type1122_window_A_recovery r
    have hZ : b6Type1122Total (b6Type1122CapacityOf x.val)=r.2.1.val := by
      unfold b6Type1122Total
      omega
    exact ⟨⟨x.val,x.property.2.2.2.2⟩,
      (b6_type1122_window_index_eq_iff ⟨x.val,x.property.2.2.2.2⟩ r).mpr
        ⟨hZ,hB,x.property.2.2.1,x.property.2.2.2.1⟩⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
#print axioms Paper7MomentCounts.b6Type1122WindowLayerEquiv

theorem b6_type1122_window_outer_guard (r : B6Type1122WindowIndex) :
    b6Type1122OuterGuard (r.2.1.val-2*r.2.2.1.val) r.2.2.1.val r.2.2.2.val r.1.val.2 := by
  have hz := (b6_type1122_mass_window_mem r.1.val.1 r.1.val.2 r.2.1.val).mp r.2.1.property
  have hs := b6_type1122_catalog_load_bounds r.1.val r.1.property
  have hC := b6_type1122_load_center_cast r.1.val.1 (by omega)
  have hc : 3 ≤ b6Type1122LoadCenter r.1.val.1 := by omega
  have hZ36 := (le_min_iff.mp hz.1.2).1
  have hZC := (le_min_iff.mp hz.1.2).2
  have hQ := (b6_type1122_q_window_iff _ _ _ hZ36 hZC).mp
    (Finset.mem_Icc.mp r.2.2.2.property)
  have hr := b6_type1122_window_A_recovery r
  unfold b6Type1122OuterGuard
  rw [hr]
  refine ⟨by omega,hQ.2.1,?_⟩
  exact (b6_type1122_guard_at_catalog_iff r.1.val r.1.property _ _).mpr
    ⟨hQ.2.2.1,hQ.2.2.2⟩
#print axioms Paper7MomentCounts.b6_type1122_window_outer_guard

theorem b6_type1122_original_count_eq_window_layers :
    Nat.card {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}=
      ∑ r : B6Type1122WindowIndex,
        b6Type1122LayerSquareSum (r.2.1.val-2*r.2.2.1.val)
          r.2.2.1.val r.2.2.2.val r.1.val.2 := by
  classical
  let e := (Equiv.sigmaFiberEquiv b6Type1122WindowIndexOf).symm.trans
    (Equiv.sigmaCongrRight b6Type1122WindowLayerEquiv)
  rw [Nat.card_congr e,Nat.card_sigma]
  exact Finset.sum_congr rfl (fun r _ =>
    b6_type1122_layer_card_eq_square_sum _ _ _ _)
#print axioms Paper7MomentCounts.b6_type1122_original_count_eq_window_layers

theorem b6_type1122_window_coefficient_terms (r : B6Type1122WindowIndex) :
    Fintype.card (Fin (r.2.2.2.val/2+1)) ≤ 10 := by
  have hz := (b6_type1122_mass_window_mem r.1.val.1 r.1.val.2 r.2.1.val).mp r.2.1.property
  have hq := (b6_type1122_q_window_iff _ _ _
    (le_min_iff.mp hz.1.2).1 (le_min_iff.mp hz.1.2).2).mp
      (Finset.mem_Icc.mp r.2.2.2.property)
  rw [Fintype.card_fin]
  omega
#print axioms Paper7MomentCounts.b6_type1122_window_coefficient_terms

end Paper7MomentCounts
