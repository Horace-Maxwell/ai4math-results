import Research.Backfill.Paper7.MomentBudgetEncoding
import Research.Backfill.Paper7.EvenMomentFeature

/-! Exact labelled counting by disjoint statistic fibres.
The existential spectral witness is tested once per fibre, never counted.
-/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

abbrev MomentStatistic := ℕ × ℕ × ℤ
#print axioms Paper7MomentCounts.MomentStatistic

def momentStatistic {b : ℕ} (x : PQ b) : MomentStatistic :=
  (weight x, qSum x, theta x)
#print axioms Paper7MomentCounts.momentStatistic

def budgetBoxes (b N : ℕ) : Finset (MomentBox b N) :=
  Finset.univ.filter (fun z => Budget b N (decodeBox z))
#print axioms Paper7MomentCounts.budgetBoxes

def attainedStatistics (b N : ℕ) : Finset MomentStatistic :=
  (budgetBoxes b N).image (fun z => momentStatistic (decodeBox z))
#print axioms Paper7MomentCounts.attainedStatistics

def statisticMultiplicity (b N : ℕ) (s : MomentStatistic) : ℕ :=
  ((budgetBoxes b N).filter (fun z => momentStatistic (decodeBox z) = s)).card
#print axioms Paper7MomentCounts.statisticMultiplicity

def acceptedStatistic (b N : ℕ) (s : MomentStatistic) : Prop :=
  ∃ a : Counts, evenFeatureCondition b N s.1 s.2.1 s.2.2 a
#print axioms Paper7MomentCounts.acceptedStatistic

theorem candB1_iff_statistic (b N : ℕ) (hb : Even b) (x : PQ b) :
    x ∈ CandB1 b N ↔ Budget b N x ∧ acceptedStatistic b N (momentStatistic x) := by
  change (Budget b N x ∧ MomentPass false true false b N x) ↔ _
  exact and_congr_right (fun _ => momentPass_iff_evenFeature b N x hb)
#print axioms Paper7MomentCounts.candB1_iff_statistic

theorem candidate_statistic_fibre (b N : ℕ) (hb : Even b) (s : MomentStatistic) :
    ((Finset.univ.filter (fun z : MomentBox b N => decodeBox z ∈ CandB1 b N)).filter
      (fun z => momentStatistic (decodeBox z) = s)) =
    if acceptedStatistic b N s then
      (budgetBoxes b N).filter (fun z => momentStatistic (decodeBox z) = s)
    else ∅ := by
  classical
  by_cases hs : acceptedStatistic b N s
  · ext z
    simp only [ite_eq_left hs, Finset.mem_filter, Finset.mem_univ, true_and,
      budgetBoxes, candB1_iff_statistic b N hb]
    constructor
    · rintro ⟨⟨hbudget, _⟩, hstat⟩
      exact ⟨hbudget, hstat⟩
    · rintro ⟨hbudget, hstat⟩
      exact ⟨⟨hbudget, hstat.symm ▸ hs⟩, hstat⟩
  · rw [ite_eq_right hs]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hrow, hstat⟩ := Finset.mem_filter.mp hz
    have hc := (Finset.mem_filter.mp hrow).2
    have hpass := ((candB1_iff_statistic b N hb (decodeBox z)).mp hc).2
    exact hs (hstat ▸ hpass)
#print axioms Paper7MomentCounts.candidate_statistic_fibre

/-- A finite histogram identity, not an evaluation of that histogram.
Different feature witnesses for one row contribute only once. -/
theorem candB1_ncard_eq_statistic_sum (b N : ℕ) (hb : Even b) :
    (CandB1 b N).ncard =
      ∑ s ∈ attainedStatistics b N,
        if acceptedStatistic b N s then statisticMultiplicity b N s else 0 := by
  classical
  rw [candB1_ncard_eq_box]
  have hmap :
      (↑(Finset.univ.filter (fun z : MomentBox b N => decodeBox z ∈ CandB1 b N)) :
        Set (MomentBox b N)).MapsTo
        (fun z => momentStatistic (decodeBox z)) (attainedStatistics b N) := by
    intro z hz
    have hc : decodeBox z ∈ CandB1 b N := (Finset.mem_filter.mp hz).2
    apply Finset.mem_image.mpr
    refine ⟨z, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.1⟩
  calc
    (Finset.univ.filter (fun z : MomentBox b N => decodeBox z ∈ CandB1 b N)).card =
        ∑ s ∈ attainedStatistics b N,
          ((Finset.univ.filter (fun z : MomentBox b N => decodeBox z ∈ CandB1 b N)).filter
            (fun z => momentStatistic (decodeBox z) = s)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [candidate_statistic_fibre b N hb s]
      by_cases hs : acceptedStatistic b N s
      · simp only [ite_eq_left hs, statisticMultiplicity]
      · simp only [ite_eq_right hs, Finset.card_empty]
#print axioms Paper7MomentCounts.candB1_ncard_eq_statistic_sum

theorem candD2_ncard_eq_statistic_sum (b N : ℕ) (hb : Even b) :
    (CandD2 b N).ncard =
      ∑ s ∈ attainedStatistics b N,
        if acceptedStatistic b N s then statisticMultiplicity b N s else 0 := by
  rw [candD2_ncard_eq_candB1_of_even b N hb]
  exact candB1_ncard_eq_statistic_sum b N hb
#print axioms Paper7MomentCounts.candD2_ncard_eq_statistic_sum

end Paper7MomentCounts
