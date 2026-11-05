import Research.Backfill.Paper7.MomentB6TenProfileCounts
import Research.Backfill.Paper7.MomentB6NineCount

/-! Source-only full original Z10 weighted slice. The template contains every
ordered capacity function in each proven histogram fibre; no multiset ordering
or catalog coverage premise is added to the original slice. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

abbrev B6TenTemplate := Σ j : Fin 14, FiniteHistogramFiber (b6TenReference j)
#print axioms Paper7MomentCounts.B6TenTemplate

def b6TenTemplateIndex (t : B6TenTemplate) : B6ZQIndex :=
  (⟨fun k => (t.2.val k).val,by
      have h := (b6TenHistogram_member_moments t.1 t.2).1
      change (∑ k, (t.2.val k).val) ≤ 36
      omega⟩,
    ⟨b6TenProfileQ t.1,by
      have h := (b6TenReference_moments t.1).2.2.1
      omega⟩)
#print axioms Paper7MomentCounts.b6TenTemplateIndex

theorem b6TenTemplateIndex_injective : Function.Injective b6TenTemplateIndex := by
  rintro ⟨j,g⟩ ⟨k,h⟩ he
  have hg : g.val = h.val := by
    funext i
    apply Fin.ext
    exact congrArg (fun r : B6ZQIndex => r.1.val i) he
  have hp : b6TenProfile j = b6TenProfile k := by
    calc
      b6TenProfile j = finiteValueHistogram (b6TenReference j) :=
        (b6TenReference_histogram j).symm
      _ = finiteValueHistogram g.val := g.property.symm
      _ = finiteValueHistogram h.val := congrArg finiteValueHistogram hg
      _ = finiteValueHistogram (b6TenReference k) := h.property
      _ = b6TenProfile k := b6TenReference_histogram k
  have hjk := b6TenProfile_injective hp
  subst k
  have gh : g = h := Subtype.ext hg
  cases gh
  rfl
#print axioms Paper7MomentCounts.b6TenTemplateIndex_injective

theorem b6TenTemplateIndex_tag (t : B6TenTemplate) :
    b6TotalZTag (b6TenTemplateIndex t) = (10 : Fin 37) := by
  apply Fin.ext
  exact (b6TenHistogram_member_moments t.1 t.2).1
#print axioms Paper7MomentCounts.b6TenTemplateIndex_tag

theorem b6TenTemplateIndex_block (t : B6TenTemplate) :
    b6ZQBlock (b6TenTemplateIndex t) = b6TenProfileWeight t.1 := by
  change (if b6ZQAccept (fun k => (t.2.val k).val) (b6TenProfileQ t.1) then
    Paper7MomentDP.boundedQDP 6 (fun k => (t.2.val k).val) (b6TenProfileQ t.1)
    else 0) = _
  rw [ite_eq_left (b6TenHistogram_member_accept t.1 t.2)]
  exact b6TenHistogram_member_weight t.1 t.2
#print axioms Paper7MomentCounts.b6TenTemplateIndex_block

def b6TenSliceWeight (r : B6ZQIndex) : ℕ :=
  if b6TotalZTag r = (10 : Fin 37) then b6ZQBlock r else 0
#print axioms Paper7MomentCounts.b6TenSliceWeight

theorem b6TenTemplateIndex_weight (t : B6TenTemplate) :
    b6TenSliceWeight (b6TenTemplateIndex t) = b6TenProfileWeight t.1 := by
  unfold b6TenSliceWeight
  rw [ite_eq_left (b6TenTemplateIndex_tag t)]
  exact b6TenTemplateIndex_block t
#print axioms Paper7MomentCounts.b6TenTemplateIndex_weight

theorem b6TenSliceWeight_complete_support (r : B6ZQIndex)
    (hne : b6TenSliceWeight r ≠ 0) : ∃ t, b6TenTemplateIndex t = r := by
  have htag : b6TotalZTag r = (10 : Fin 37) := by
    by_contra hn
    exact hne (ite_eq_right hn)
  have hZ : (∑ i, r.1.val i) = 10 := congrArg Fin.val htag
  have hb : b6ZQBlock r ≠ 0 := by
    intro hz
    apply hne
    simp only [b6TenSliceWeight,ite_eq_left htag,hz]
  obtain ⟨hQ1,hQ10,hM,_hlarge⟩ := b6_ten_nonzero_block_full_reduction r htag hb
  obtain ⟨j,e,hz,hq⟩ := b6_ten_guard_histogram_cover r.1.val r.2.val hZ hQ10 ⟨hQ1,hM⟩
  let g : FiniteHistogramFiber (b6TenReference j) :=
    ⟨b6TenReference j ∘ e,finiteValueHistogram_comp_perm (b6TenReference j) e⟩
  refine ⟨⟨j,g⟩,?_⟩
  exact Prod.ext (Subtype.ext hz.symm) (Fin.ext hq.symm)
#print axioms Paper7MomentCounts.b6TenSliceWeight_complete_support

theorem b6TenTemplateWeight_sum :
    (∑ t : B6TenTemplate, b6TenProfileWeight t.1) = 7485 := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,b6TenHistogram_member_card]
  exact b6TenProfile_weighted_sum
#print axioms Paper7MomentCounts.b6TenTemplateWeight_sum

theorem b6LabelledZSlice_ten_eq_sevenThousandFourHundredEightyFive :
    b6LabelledZSlice 10 = 7485 := by
  change (∑ r, b6TenSliceWeight r) = 7485
  rw [finite_sum_eq_sum_of_injective_support b6TenSliceWeight b6TenTemplateIndex
    b6TenTemplateIndex_injective b6TenSliceWeight_complete_support]
  simp only [b6TenTemplateIndex_weight]
  exact b6TenTemplateWeight_sum
#print axioms Paper7MomentCounts.b6LabelledZSlice_ten_eq_sevenThousandFourHundredEightyFive

end Paper7MomentCounts
