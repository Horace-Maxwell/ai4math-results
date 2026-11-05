import Research.Backfill.Paper7.MomentB6ThreePairWeights

/-! Full original repeated-three-position fibre and its true multiplicities.
No final labelled or canonical count is used as a premise or subtraction. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy Paper7MomentDP
open scoped BigOperators Classical

abbrev B6ThreePairZQCandidate :=
  {x : ZQCoordinates 3 // B6ThreePairGuard x.val.1 (∑ i,x.val.2 i)}
#print axioms Paper7MomentCounts.B6ThreePairZQCandidate

abbrev B6ThreePairTemplate := Σ j : Fin 16,
  Σ g : FiniteHistogramFiber (b6ThreePairReference j),
    BoundedQFibre (fun i => (g.val i).val) (b6ThreePairQ j)
#print axioms Paper7MomentCounts.B6ThreePairTemplate

def b6ThreePairTemplateData (t : B6ThreePairTemplate) : ZQCoordinates 3 :=
  ⟨((fun i => (t.2.1.val i).val),(fun i => (t.2.2.val i).val)),
    fun i => Nat.le_of_lt_succ (t.2.2.val i).isLt⟩
#print axioms Paper7MomentCounts.b6ThreePairTemplateData

theorem b6ThreePairTemplateData_accept (t : B6ThreePairTemplate) :
    B6ThreePairGuard (b6ThreePairTemplateData t).val.1
      (∑ i,(b6ThreePairTemplateData t).val.2 i) := by
  have hQ : (∑ i,(t.2.2.val i).val) = b6ThreePairQ t.1 := t.2.2.property
  change B6ThreePairGuard (fun i => (t.2.1.val i).val) (∑ i,(t.2.2.val i).val)
  rw [hQ]
  exact b6ThreePairHistogram_accept t.1 t.2.1
#print axioms Paper7MomentCounts.b6ThreePairTemplateData_accept

def b6ThreePairTemplateMap (t : B6ThreePairTemplate) : B6ThreePairZQCandidate :=
  ⟨b6ThreePairTemplateData t,b6ThreePairTemplateData_accept t⟩
#print axioms Paper7MomentCounts.b6ThreePairTemplateMap

theorem b6ThreePairTemplateMap_injective : Function.Injective b6ThreePairTemplateMap := by
  rintro ⟨j,g,q⟩ ⟨k,h,r⟩ he
  have hz : g.val = h.val := by
    funext i
    apply Fin.ext
    exact congrArg (fun y : B6ThreePairZQCandidate => y.val.val.1 i) he
  have hsum := congrArg (fun y : B6ThreePairZQCandidate => ∑ i,y.val.val.2 i) he
  have hQ : b6ThreePairQ j = b6ThreePairQ k :=
    q.property.symm.trans (hsum.trans r.property)
  have hh : finiteValueHistogram (b6ThreePairReference j) =
      finiteValueHistogram (b6ThreePairReference k) :=
    g.property.symm.trans ((congrArg finiteValueHistogram hz).trans h.property)
  have hsig : b6ThreePairSignature j = b6ThreePairSignature k := by
    change (finiteValueHistogram (b6ThreePairReference j),b6ThreePairQ j) =
      (finiteValueHistogram (b6ThreePairReference k),b6ThreePairQ k)
    exact Prod.ext hh hQ
  have hjk : j = k := b6ThreePairSignature_injective hsig
  subst k
  have hg : g = h := Subtype.ext hz
  subst h
  have hqr : q = r := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun y : B6ThreePairZQCandidate => y.val.val.2 i) he
  subst r
  rfl
#print axioms Paper7MomentCounts.b6ThreePairTemplateMap_injective

theorem b6ThreePairTemplateMap_surjective : Function.Surjective b6ThreePairTemplateMap := by
  intro x
  obtain ⟨j,e,hz,hQ⟩ := b6_three_pair_guard_cover x.val.val.1 (∑ i,x.val.val.2 i) x.property
  let g : FiniteHistogramFiber (b6ThreePairReference j) :=
    ⟨b6ThreePairReference j ∘ e,finiteValueHistogram_comp_perm (b6ThreePairReference j) e⟩
  have hzval (i : Fin 3) : x.val.val.1 i = (g.val i).val := congrFun hz i
  let q : BoundedQFibre (fun i => (g.val i).val) (b6ThreePairQ j) :=
    ⟨fun i => ⟨x.val.val.2 i,by
      apply Nat.lt_succ_of_le
      change x.val.val.2 i ≤ (g.val i).val
      exact (x.val.property i).trans_eq (hzval i)⟩,hQ⟩
  refine ⟨⟨j,g,q⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · funext i
    exact (hzval i).symm
  · rfl
#print axioms Paper7MomentCounts.b6ThreePairTemplateMap_surjective

def b6ThreePairTemplateEquiv : B6ThreePairTemplate ≃ B6ThreePairZQCandidate :=
  Equiv.ofBijective b6ThreePairTemplateMap
    ⟨b6ThreePairTemplateMap_injective,b6ThreePairTemplateMap_surjective⟩
#print axioms Paper7MomentCounts.b6ThreePairTemplateEquiv

theorem b6ThreePairTemplate_card : Nat.card B6ThreePairTemplate = 129 := by
  calc
    Nat.card B6ThreePairTemplate = ∑ j : Fin 16,
        Nat.card (Σ g : FiniteHistogramFiber (b6ThreePairReference j),
          BoundedQFibre (fun i => (g.val i).val) (b6ThreePairQ j)) := Nat.card_sigma
    _ = ∑ j : Fin 16, ∑ g : FiniteHistogramFiber (b6ThreePairReference j),
        Nat.card (BoundedQFibre (fun i => (g.val i).val) (b6ThreePairQ j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Nat.card_sigma
    _ = ∑ j : Fin 16,b6ThreePairCard j*b6ThreePairWeight j := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [b6ThreePairHistogram_weight,Finset.sum_const,Finset.card_univ,
        smul_eq_mul,b6ThreePairHistogram_card]
    _ = 129 := b6ThreePair_weighted_sum
#print axioms Paper7MomentCounts.b6ThreePairTemplate_card

def b6ThreePairPQEquiv :
    {x : PQ 3 // b6ThreePairRow x ∈ CandB1 6 42} ≃ B6ThreePairZQCandidate where
  toFun x := ⟨pqToZQ x.val,by
    apply (b6_three_pair_zq_accept (pqToZQ x.val)).mp
    have hb : zqToPQ (pqToZQ x.val) = x.val := (pqEquivZQ 3).left_inv x.val
    rw [hb]
    exact x.property⟩
  invFun x := ⟨zqToPQ x.val,(b6_three_pair_zq_accept x.val).mpr x.property⟩
  left_inv x := Subtype.ext ((pqEquivZQ 3).left_inv x.val)
  right_inv x := Subtype.ext ((pqEquivZQ 3).right_inv x.val)
#print axioms Paper7MomentCounts.b6ThreePairPQEquiv

theorem b6_three_pair_compressed_ncard :
    {x : PQ 3 | b6ThreePairRow x ∈ CandB1 6 42}.ncard = 129 := by
  change Nat.card {x : PQ 3 // b6ThreePairRow x ∈ CandB1 6 42} = _
  rw [Nat.card_congr b6ThreePairPQEquiv,← Nat.card_congr b6ThreePairTemplateEquiv]
  exact b6ThreePairTemplate_card
#print axioms Paper7MomentCounts.b6_three_pair_compressed_ncard

theorem b6ThreePairRow_injective : Function.Injective b6ThreePairRow := by
  intro x y he
  have hp0 := congrArg (fun w : PQ 6 => w.1 0) he
  have hp1 := congrArg (fun w : PQ 6 => w.1 1) he
  have hp2 := congrArg (fun w : PQ 6 => w.1 2) he
  have hq0 := congrArg (fun w : PQ 6 => w.2 0) he
  have hq1 := congrArg (fun w : PQ 6 => w.2 1) he
  have hq2 := congrArg (fun w : PQ 6 => w.2 2) he
  apply Prod.ext
  · funext i
    fin_cases i
    · exact hp0
    · exact hp1
    · exact hp2
  · funext i
    fin_cases i
    · exact hq0
    · exact hq1
    · exact hq2
#print axioms Paper7MomentCounts.b6ThreePairRow_injective

def b6ThreePairFullFibreEquiv :
    {y : PQ 3 // b6ThreePairRow y ∈ CandB1 6 42} ≃
      {x : PQ 6 // x ∈ CandB1 6 42 ∧ ∃ y : PQ 3,x = b6ThreePairRow y} :=
  Equiv.ofBijective (fun y => ⟨b6ThreePairRow y.val,y.property,⟨y.val,rfl⟩⟩) (by
    constructor
    · intro a b h
      apply Subtype.ext
      exact b6ThreePairRow_injective (congrArg Subtype.val h)
    · rintro ⟨x,hx,y,rfl⟩
      exact ⟨⟨y,hx⟩,rfl⟩)
#print axioms Paper7MomentCounts.b6ThreePairFullFibreEquiv

theorem b6_three_pair_candB1_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ ∃ y : PQ 3,x = b6ThreePairRow y}.ncard = 129 := by
  change Nat.card {x : PQ 6 // x ∈ CandB1 6 42 ∧ ∃ y : PQ 3,x = b6ThreePairRow y} = _
  rw [← Nat.card_congr b6ThreePairFullFibreEquiv]
  exact b6_three_pair_compressed_ncard
#print axioms Paper7MomentCounts.b6_three_pair_candB1_ncard

theorem b6_three_pair_candD2_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ ∃ y : PQ 3,x = b6ThreePairRow y}.ncard = 129 := by
  rw [candD2_eq_candB1_of_even 6 42 (by decide)]
  exact b6_three_pair_candB1_ncard
#print axioms Paper7MomentCounts.b6_three_pair_candD2_ncard

end Paper7MomentCounts
