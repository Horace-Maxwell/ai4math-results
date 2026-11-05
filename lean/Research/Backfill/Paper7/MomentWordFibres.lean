import Research.Backfill.Paper7.FiniteWordCountDP
import Research.Backfill.Paper7.MomentStatisticFibres

/-! The original PQ statistic fibres, with their actual budget, are the fibres
of a finite-alphabet word sum. This gives an exact DP formula and performs no
numeric evaluation. The existential spectral feature remains a predicate. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy Paper7MomentDP
open scoped BigOperators Classical

abbrev MomentLetter (b N : ℕ) := Fin (N-b+1) × Fin ((N-b)/2+1)
#print axioms Paper7MomentCounts.MomentLetter

def decodeWord {b N : ℕ} (w : Fin b → MomentLetter b N) : PQ b :=
  (fun i => (w i).1.val, fun i => (w i).2.val)
#print axioms Paper7MomentCounts.decodeWord

theorem budget_coordinate_bounds (b N : ℕ) (x : PQ b) (hx : Budget b N x)
    (i : Fin b) : x.1 i ≤ N-b ∧ x.2 i ≤ (N-b)/2 := by
  have hp : x.1 i ≤ pSum x :=
    Finset.single_le_sum (f := x.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hq : x.2 i ≤ qSum x :=
    Finset.single_le_sum (f := x.2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact ⟨hp.trans (budget_sum_bounds b N x hx).1,
    hq.trans (budget_sum_bounds b N x hx).2⟩
#print axioms Paper7MomentCounts.budget_coordinate_bounds

def encodeBudgetWord (b N : ℕ) (x : {x : PQ b // Budget b N x}) :
    Fin b → MomentLetter b N := fun i =>
  (⟨x.val.1 i, Nat.lt_succ_of_le (budget_coordinate_bounds b N x.val x.property i).1⟩,
   ⟨x.val.2 i, Nat.lt_succ_of_le (budget_coordinate_bounds b N x.val x.property i).2⟩)
#print axioms Paper7MomentCounts.encodeBudgetWord

theorem decode_encodeBudgetWord (b N : ℕ) (x : {x : PQ b // Budget b N x}) :
    decodeWord (encodeBudgetWord b N x) = x.val := rfl
#print axioms Paper7MomentCounts.decode_encodeBudgetWord

def predicateWordEquiv (b N : ℕ) (H : PQ b → Prop)
    (hH : ∀ x, H x → Budget b N x) :
    {x : PQ b // H x} ≃ {w : Fin b → MomentLetter b N // H (decodeWord w)} where
  toFun x := ⟨encodeBudgetWord b N ⟨x.val, hH x.val x.property⟩, x.property⟩
  invFun w := ⟨decodeWord w.val, w.property⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    funext i
    apply Prod.ext <;> apply Fin.ext <;> rfl
#print axioms Paper7MomentCounts.predicateWordEquiv

abbrev IntegerStatistic := ℤ × ℤ × ℤ
#print axioms Paper7MomentCounts.IntegerStatistic

def castStatistic (s : MomentStatistic) : IntegerStatistic := (s.1, s.2.1, s.2.2)
#print axioms Paper7MomentCounts.castStatistic

theorem castStatistic_injective : Function.Injective castStatistic := by
  intro s t h
  apply Prod.ext
  · have h1 := congrArg (fun z : IntegerStatistic => z.1) h
    change (s.1 : ℤ) = (t.1 : ℤ) at h1
    exact_mod_cast h1
  · apply Prod.ext
    · have h2 := congrArg (fun z : IntegerStatistic => z.2.1) h
      change (s.2.1 : ℤ) = (t.2.1 : ℤ) at h2
      exact_mod_cast h2
    · exact congrArg (fun z : IntegerStatistic => z.2.2) h
#print axioms Paper7MomentCounts.castStatistic_injective

def letterStatistic {b N : ℕ} (a : MomentLetter b N) : IntegerStatistic :=
  ((a.1.val + 2*a.2.val : ℕ), a.2.val, thetaV a.1.val a.2.val)
#print axioms Paper7MomentCounts.letterStatistic

theorem wordSum_letterStatistic (b N : ℕ) (w : Fin b → MomentLetter b N) :
    wordSum letterStatistic w = castStatistic (momentStatistic (decodeWord w)) := by
  simp [wordSum, letterStatistic, castStatistic, momentStatistic, decodeWord,
    weight, pSum, qSum, theta, ← prod_mk_sum, Finset.sum_add_distrib, Finset.mul_sum]
#print axioms Paper7MomentCounts.wordSum_letterStatistic

/-- The budget in this equivalence is proved from the requested total weight.
No separate budget test or feature witness is counted by the word DP. -/
def statisticWordEquiv (b N : ℕ) (s : MomentStatistic)
    (hs : 0 < s.1 ∧ b+s.1 ≤ N) :
    {x : PQ b // Budget b N x ∧ momentStatistic x = s} ≃
      {w : Fin b → MomentLetter b N // wordSum letterStatistic w = castStatistic s} :=
  (predicateWordEquiv b N (fun x => Budget b N x ∧ momentStatistic x = s)
    (fun _ hx => hx.1)).trans (Equiv.subtypeEquivRight fun w => by
      constructor
      · intro hw
        rw [wordSum_letterStatistic b N w, hw.2]
      · intro hw
        have he : momentStatistic (decodeWord w) = s := castStatistic_injective (by
          rw [← wordSum_letterStatistic b N w]
          exact hw)
        refine ⟨?_, he⟩
        change 0 < weight (decodeWord w) ∧ b + weight (decodeWord w) ≤ N
        have hweight : weight (decodeWord w) = s.1 := congrArg Prod.fst he
        rw [hweight]
        exact hs)
#print axioms Paper7MomentCounts.statisticWordEquiv

theorem statisticMultiplicity_eq_wordCountDP (b N : ℕ) (s : MomentStatistic)
    (hs : 0 < s.1 ∧ b+s.1 ≤ N) :
    statisticMultiplicity b N s =
      wordCountDP (letterStatistic (b := b) (N := N)) b (castStatistic s) := by
  classical
  let H : PQ b → Prop := fun x => Budget b N x ∧ momentStatistic x = s
  have hc := predicate_ncard_eq_box_filter b N H (fun _ hx => hx.1)
  change Nat.card {x : PQ b // H x} = _ at hc
  calc
    statisticMultiplicity b N s =
        (Finset.univ.filter (fun z : MomentBox b N => H (decodeBox z))).card := by
      unfold statisticMultiplicity budgetBoxes
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, H]
    _ = Nat.card {x : PQ b // H x} := by
      convert hc.symm using 1
      apply congrArg Finset.card
      apply Finset.ext
      intro z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ = wordFibreCard (letterStatistic (b := b) (N := N)) b (castStatistic s) :=
      Nat.card_congr (statisticWordEquiv b N s hs)
    _ = _ := (wordCountDP_eq_card _ _ _).symm
#print axioms Paper7MomentCounts.statisticMultiplicity_eq_wordCountDP

theorem attainedStatistic_budget (b N : ℕ) (s : MomentStatistic)
    (hs : s ∈ attainedStatistics b N) : 0 < s.1 ∧ b+s.1 ≤ N := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hs
  exact (Finset.mem_filter.mp hz).2
#print axioms Paper7MomentCounts.attainedStatistic_budget

/-- Exact original labelled cardinality as disjoint DP fibres. This is not a
numeric certificate or a claim about running the unmemoized recurrence. -/
theorem candB1_ncard_eq_wordCountDP_sum (b N : ℕ) (hb : Even b) :
    (CandB1 b N).ncard = ∑ s ∈ attainedStatistics b N,
      if acceptedStatistic b N s then
        wordCountDP (letterStatistic (b := b) (N := N)) b (castStatistic s) else 0 := by
  rw [candB1_ncard_eq_statistic_sum b N hb]
  apply Finset.sum_congr rfl
  intro s hs
  rw [statisticMultiplicity_eq_wordCountDP b N s (attainedStatistic_budget b N s hs)]
#print axioms Paper7MomentCounts.candB1_ncard_eq_wordCountDP_sum

theorem candD2_ncard_eq_wordCountDP_sum (b N : ℕ) (hb : Even b) :
    (CandD2 b N).ncard = ∑ s ∈ attainedStatistics b N,
      if acceptedStatistic b N s then
        wordCountDP (letterStatistic (b := b) (N := N)) b (castStatistic s) else 0 := by
  rw [candD2_ncard_eq_candB1_of_even b N hb]
  exact candB1_ncard_eq_wordCountDP_sum b N hb
#print axioms Paper7MomentCounts.candD2_ncard_eq_wordCountDP_sum

end Paper7MomentCounts
