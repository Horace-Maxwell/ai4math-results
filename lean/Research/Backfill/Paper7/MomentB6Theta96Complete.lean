import Research.Backfill.Paper7.MomentB6Theta96Weights

/-! Complete original labelled theta96 fibre. Every index is a genuine
ordered capacity vector and Q, every q multiplicity uses the original PQ
fibre equivalence, and each surviving histogram is counted once. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b6ZQTheta (r : B6ZQIndex) : ℤ :=
  12 + 3*((∑ i, r.1.val i : ℕ) : ℤ) + 2*(r.2.val : ℤ) +
    ∑ i, (r.1.val i : ℤ)^2
#print axioms Paper7MomentCounts.b6ZQTheta

theorem b6OriginalZQFibre_theta (r : B6ZQIndex) (x : B6OriginalZQFibre r) :
    theta x.val = b6ZQTheta r := by
  have h := b6_zq_theta (pqToZQ x.val)
  have hb : zqToPQ (pqToZQ x.val) = x.val := (pqEquivZQ 6).left_inv x.val
  have hz : (pqToZQ x.val).val.1 = r.1.val := funext x.property.1
  have hq : (∑ i, (pqToZQ x.val).val.2 i) = r.2.val := x.property.2.1
  rw [hb,hz,hq] at h
  exact h
#print axioms Paper7MomentCounts.b6OriginalZQFibre_theta

def b6Theta96Block (r : B6ZQIndex) : ℕ :=
  if b6ZQTheta r = 96 then b6ZQBlock r else 0
#print axioms Paper7MomentCounts.b6Theta96Block

abbrev B6Theta96OriginalFibre (r : B6ZQIndex) :=
  {x : B6OriginalZQFibre r // theta x.val = 96}
#print axioms Paper7MomentCounts.B6Theta96OriginalFibre

theorem b6Theta96OriginalFibre_card (r : B6ZQIndex) :
    Nat.card (B6Theta96OriginalFibre r) = b6Theta96Block r := by
  by_cases ht : b6ZQTheta r = 96
  · have e : B6Theta96OriginalFibre r ≃ B6OriginalZQFibre r := {
      toFun := fun x => x.val
      invFun := fun x => ⟨x,(b6OriginalZQFibre_theta r x).trans ht⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr e,b6Theta96Block,ite_eq_left ht]
    exact b6OriginalZQFibre_card r
  · let : IsEmpty (B6Theta96OriginalFibre r) := ⟨by
      intro x
      exact ht ((b6OriginalZQFibre_theta r x.val).symm.trans x.property)⟩
    rw [Nat.card_of_isEmpty,b6Theta96Block,ite_eq_right ht]
#print axioms Paper7MomentCounts.b6Theta96OriginalFibre_card

abbrev B6Theta96Candidate := {x : PQ 6 // x ∈ CandB1 6 42 ∧ theta x = 96}
#print axioms Paper7MomentCounts.B6Theta96Candidate

def b6Theta96CandidateIndex (x : B6Theta96Candidate) : B6ZQIndex :=
  b6CandidateIndex ⟨x.val,x.property.1⟩
#print axioms Paper7MomentCounts.b6Theta96CandidateIndex

def b6Theta96IndexFibreEquiv (r : B6ZQIndex) :
    {x : B6Theta96Candidate // b6Theta96CandidateIndex x = r} ≃
      B6Theta96OriginalFibre r where
  toFun x := ⟨⟨x.val.val,
    ((b6CandidateIndex_eq_iff ⟨x.val.val,x.val.property.1⟩ r).mp x.property).1,
    ((b6CandidateIndex_eq_iff ⟨x.val.val,x.val.property.1⟩ r).mp x.property).2,
    x.val.property.1⟩,x.val.property.2⟩
  invFun x := ⟨⟨x.val.val,x.val.property.2.2,x.property⟩,
    (b6CandidateIndex_eq_iff ⟨x.val.val,x.val.property.2.2⟩ r).mpr
      ⟨x.val.property.1,x.val.property.2.1⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
#print axioms Paper7MomentCounts.b6Theta96IndexFibreEquiv

def b6Theta96CandidatePartitionEquiv :
    B6Theta96Candidate ≃ Σ r : B6ZQIndex, B6Theta96OriginalFibre r :=
  (Equiv.sigmaFiberEquiv b6Theta96CandidateIndex).symm.trans
    (Equiv.sigmaCongrRight b6Theta96IndexFibreEquiv)
#print axioms Paper7MomentCounts.b6Theta96CandidatePartitionEquiv

theorem b6_candB1_theta96_ncard_eq_sum :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 96}.ncard =
      ∑ r : B6ZQIndex, b6Theta96Block r := by
  change Nat.card B6Theta96Candidate = _
  calc
    Nat.card B6Theta96Candidate =
        Nat.card (Σ r : B6ZQIndex, B6Theta96OriginalFibre r) :=
      Nat.card_congr b6Theta96CandidatePartitionEquiv
    _ = ∑ r : B6ZQIndex, Nat.card (B6Theta96OriginalFibre r) := Nat.card_sigma
    _ = ∑ r : B6ZQIndex, b6Theta96Block r :=
      Finset.sum_congr rfl (fun r _ => b6Theta96OriginalFibre_card r)
#print axioms Paper7MomentCounts.b6_candB1_theta96_ncard_eq_sum

theorem b6Theta96Histogram_data (j : Fin 54)
    (g : FiniteHistogramFiber (b6Theta96Reference j)) :
    B6Theta96Data (fun i => (g.val i).val) (b6Theta96Q j) := by
  obtain ⟨e,he⟩ := finiteValueHistogram_exists_perm (b6Theta96Reference j) g.val g.property
  have hz : (∑ i, (g.val i).val) = ∑ i, b6Theta96Nat j i := by
    rw [he]
    exact Equiv.sum_comp e (b6Theta96Nat j)
  have hs : (∑ i, (g.val i).val^2) = ∑ i, (b6Theta96Nat j i)^2 := by
    rw [he]
    exact Equiv.sum_comp e (fun i => (b6Theta96Nat j i)^2)
  simpa only [B6Theta96Data,hz,hs] using b6Theta96Reference_data j
#print axioms Paper7MomentCounts.b6Theta96Histogram_data

theorem b6Theta96Histogram_weight (j : Fin 54)
    (g : FiniteHistogramFiber (b6Theta96Reference j)) :
    Paper7MomentDP.boundedQDP 6 (fun i => (g.val i).val) (b6Theta96Q j) =
      b6Theta96Weight j := by
  obtain ⟨e,he⟩ := finiteValueHistogram_exists_perm (b6Theta96Reference j) g.val g.property
  have hn : (fun i => (g.val i).val) = b6Theta96Nat j ∘ e := by
    funext i
    exact congrArg Fin.val (congrFun he i)
  rw [hn,Paper7MomentReduction.boundedQDP_comp_perm]
  exact b6Theta96Reference_weight j
#print axioms Paper7MomentCounts.b6Theta96Histogram_weight

abbrev B6Theta96Template := Σ j : Fin 54, FiniteHistogramFiber (b6Theta96Reference j)
#print axioms Paper7MomentCounts.B6Theta96Template

def b6Theta96TemplateIndex (t : B6Theta96Template) : B6ZQIndex :=
  (⟨fun i => (t.2.val i).val,by
      have h := (b6Theta96Histogram_data t.1 t.2).2.1
      change (∑ i, (t.2.val i).val) ≤ 13 at h
      change (∑ i, (t.2.val i).val) ≤ 36
      exact h.trans (by norm_num)⟩,
    ⟨b6Theta96Q t.1,by
      have h := b6Theta96Histogram_data t.1 t.2
      have hz := h.2.1
      have hq := h.2.2.1
      omega⟩)
#print axioms Paper7MomentCounts.b6Theta96TemplateIndex

theorem b6Theta96TemplateIndex_injective : Function.Injective b6Theta96TemplateIndex := by
  rintro ⟨j,g⟩ ⟨k,h⟩ he
  have hg : g.val = h.val := by
    funext i
    apply Fin.ext
    exact congrArg (fun r : B6ZQIndex => r.1.val i) he
  have hp : b6Theta96Profile j = b6Theta96Profile k := by
    calc
      b6Theta96Profile j = finiteValueHistogram (b6Theta96Reference j) :=
        (b6Theta96Reference_histogram j).symm
      _ = finiteValueHistogram g.val := g.property.symm
      _ = finiteValueHistogram h.val := congrArg finiteValueHistogram hg
      _ = finiteValueHistogram (b6Theta96Reference k) := h.property
      _ = b6Theta96Profile k := b6Theta96Reference_histogram k
  have hjk := b6Theta96Profile_injective hp
  subst k
  have gh : g = h := Subtype.ext hg
  cases gh
  rfl
#print axioms Paper7MomentCounts.b6Theta96TemplateIndex_injective

theorem b6Theta96TemplateIndex_weight (t : B6Theta96Template) :
    b6Theta96Block (b6Theta96TemplateIndex t) = b6Theta96Weight t.1 := by
  have hd := b6Theta96Histogram_data t.1 t.2
  obtain ⟨ha,ht⟩ := b6_theta96_accept_of_data _ _ hd
  change (if 12 + 3*((∑ i, (t.2.val i).val : ℕ) : ℤ) +
      2*(b6Theta96Q t.1 : ℤ) + ∑ i, ((t.2.val i).val : ℤ)^2 = 96 then
      (if b6ZQAccept (fun i => (t.2.val i).val) (b6Theta96Q t.1) then
        Paper7MomentDP.boundedQDP 6 (fun i => (t.2.val i).val) (b6Theta96Q t.1)
        else 0) else 0) = _
  rw [ite_eq_left ht,ite_eq_left ha]
  exact b6Theta96Histogram_weight t.1 t.2
#print axioms Paper7MomentCounts.b6Theta96TemplateIndex_weight

theorem b6Theta96Block_complete_support (r : B6ZQIndex)
    (hne : b6Theta96Block r ≠ 0) : ∃ t, b6Theta96TemplateIndex t = r := by
  have ht : b6ZQTheta r = 96 := by
    by_contra hn
    exact hne (ite_eq_right hn)
  have hb : b6ZQBlock r ≠ 0 := by
    intro hz
    apply hne
    simp only [b6Theta96Block,ite_eq_left ht,hz]
  have ha : b6ZQAccept r.1.val r.2.val := by
    by_contra hn
    exact hb (ite_eq_right hn)
  have hQ : r.2.val ≤ ∑ i, r.1.val i := by
    by_contra hn
    exact hb (b6ZQBlock_zero_of_Q_above_capacity r (by omega))
  have hd := b6_theta96_data_of_accept r.1.val r.2.val hQ ha ht
  obtain ⟨j,e,hz,hq⟩ := b6_theta96_histogram_cover r.1.val r.2.val hd
  let g : FiniteHistogramFiber (b6Theta96Reference j) :=
    ⟨b6Theta96Reference j ∘ e,finiteValueHistogram_comp_perm (b6Theta96Reference j) e⟩
  refine ⟨⟨j,g⟩,?_⟩
  exact Prod.ext (Subtype.ext hz.symm) (Fin.ext hq.symm)
#print axioms Paper7MomentCounts.b6Theta96Block_complete_support

theorem b6Theta96TemplateWeight_sum :
    (∑ t : B6Theta96Template, b6Theta96Weight t.1) = 53903 := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,b6Theta96Histogram_card]
  exact b6Theta96_weighted_sum
#print axioms Paper7MomentCounts.b6Theta96TemplateWeight_sum

theorem b6Theta96Block_sum : (∑ r : B6ZQIndex, b6Theta96Block r) = 53903 := by
  rw [finite_sum_eq_sum_of_injective_support b6Theta96Block b6Theta96TemplateIndex
    b6Theta96TemplateIndex_injective b6Theta96Block_complete_support]
  simp only [b6Theta96TemplateIndex_weight]
  exact b6Theta96TemplateWeight_sum
#print axioms Paper7MomentCounts.b6Theta96Block_sum

theorem b6_candB1_theta96_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 96}.ncard = 53903 := by
  rw [b6_candB1_theta96_ncard_eq_sum,b6Theta96Block_sum]
#print axioms Paper7MomentCounts.b6_candB1_theta96_ncard

theorem b6_candD2_theta96_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 96}.ncard = 53903 := by
  rw [candD2_eq_candB1_of_even 6 42 (by decide)]
  exact b6_candB1_theta96_ncard
#print axioms Paper7MomentCounts.b6_candD2_theta96_ncard

end Paper7MomentCounts
