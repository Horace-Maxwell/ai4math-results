import Research.Backfill.Paper7.LegacyCandidates
import Research.Backfill.Paper7.BudgetTupleCounts

/-! Exact finite encoding of the original moment-candidate sets.
This source supplies finite sets and cardinal formulas, not the four numeric counts.
-/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

abbrev MomentBox (b N : ℕ) :=
  Paper7Budget.BoundedTuple b (N - b) ×
    Paper7Budget.BoundedTuple b ((N - b) / 2)
#print axioms Paper7MomentCounts.MomentBox

def decodeBox {b N : ℕ} (z : MomentBox b N) : PQ b := (z.1.val, z.2.val)
#print axioms Paper7MomentCounts.decodeBox

theorem budget_sum_bounds (b N : ℕ) (x : PQ b) (hx : Budget b N x) :
    pSum x ≤ N - b ∧ qSum x ≤ (N - b) / 2 := by
  have h := hx.2
  change b + (pSum x + 2 * qSum x) ≤ N at h
  omega
#print axioms Paper7MomentCounts.budget_sum_bounds

def encodeBudget (b N : ℕ) (x : {x : PQ b // Budget b N x}) : MomentBox b N :=
  (⟨x.val.1, (budget_sum_bounds b N x.val x.property).1⟩,
    ⟨x.val.2, (budget_sum_bounds b N x.val x.property).2⟩)
#print axioms Paper7MomentCounts.encodeBudget

theorem decode_encodeBudget (b N : ℕ) (x : {x : PQ b // Budget b N x}) :
    decodeBox (encodeBudget b N x) = x.val := rfl
#print axioms Paper7MomentCounts.decode_encodeBudget

theorem encodeBudget_injective (b N : ℕ) : Function.Injective (encodeBudget b N) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (decodeBox (b := b) (N := N)) h
#print axioms Paper7MomentCounts.encodeBudget_injective

theorem budget_finite (b N : ℕ) : {x : PQ b | Budget b N x}.Finite := by
  change Finite {x : PQ b // Budget b N x}
  exact Finite.of_injective (encodeBudget b N) (encodeBudget_injective b N)
#print axioms Paper7MomentCounts.budget_finite

/-- This equivalence retains the entire predicate; it neither prunes nor
identifies two different canonical conventions. -/
def predicateBoxEquiv (b N : ℕ) (H : PQ b → Prop)
    (hH : ∀ x, H x → Budget b N x) :
    {x : PQ b // H x} ≃ {z : MomentBox b N // H (decodeBox z)} where
  toFun x := ⟨encodeBudget b N ⟨x.val, hH x.val x.property⟩, x.property⟩
  invFun z := ⟨decodeBox z.val, z.property⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
#print axioms Paper7MomentCounts.predicateBoxEquiv

theorem predicate_ncard_eq_box_filter (b N : ℕ) (H : PQ b → Prop)
    (hH : ∀ x, H x → Budget b N x) :
    {x : PQ b | H x}.ncard =
      (Finset.univ.filter (fun z : MomentBox b N => H (decodeBox z))).card := by
  classical
  change Nat.card {x : PQ b // H x} = _
  calc
    Nat.card {x : PQ b // H x} =
        Nat.card {z : MomentBox b N // H (decodeBox z)} :=
      Nat.card_congr (predicateBoxEquiv b N H hH)
    _ = Fintype.card {z : MomentBox b N // H (decodeBox z)} :=
      Nat.card_eq_fintype_card
    _ = _ := Fintype.card_subtype _
#print axioms Paper7MomentCounts.predicate_ncard_eq_box_filter

theorem momentBox_card (b N : ℕ) :
    Fintype.card (MomentBox b N) =
      (N - b + b).choose b * ((N - b) / 2 + b).choose b := by
  rw [Fintype.card_prod, Paper7Budget.card_boundedTuple,
    Paper7Budget.card_boundedTuple]
#print axioms Paper7MomentCounts.momentBox_card

theorem candB1_finite (b N : ℕ) : (CandB1 b N).Finite := by
  exact (budget_finite b N).subset (fun _ hx => hx.1)
#print axioms Paper7MomentCounts.candB1_finite

theorem canonB1_finite (b N : ℕ) : (canonB1 b N).Finite := by
  exact (candB1_finite b N).subset (fun _ hx => hx.1)
#print axioms Paper7MomentCounts.canonB1_finite

theorem candD2_finite (b N : ℕ) : (CandD2 b N).Finite := by
  exact (budget_finite b N).subset (fun _ hx => hx.1)
#print axioms Paper7MomentCounts.candD2_finite

theorem canonD2_finite (b N : ℕ) : (canonD2 b N).Finite := by
  exact (candD2_finite b N).subset (fun _ hx => hx.1)
#print axioms Paper7MomentCounts.canonD2_finite

theorem candB1_ncard_eq_box (b N : ℕ) :
    (CandB1 b N).ncard =
      (Finset.univ.filter (fun z : MomentBox b N => decodeBox z ∈ CandB1 b N)).card := by
  exact predicate_ncard_eq_box_filter b N (fun x => x ∈ CandB1 b N)
    (fun _ hx => hx.1)
#print axioms Paper7MomentCounts.candB1_ncard_eq_box

theorem canonB1_ncard_eq_box (b N : ℕ) :
    (canonB1 b N).ncard =
      (Finset.univ.filter (fun z : MomentBox b N => decodeBox z ∈ canonB1 b N)).card := by
  exact predicate_ncard_eq_box_filter b N (fun x => x ∈ canonB1 b N)
    (fun _ hx => hx.1.1)
#print axioms Paper7MomentCounts.canonB1_ncard_eq_box

theorem candD2_ncard_eq_box (b N : ℕ) :
    (CandD2 b N).ncard =
      (Finset.univ.filter (fun z : MomentBox b N => decodeBox z ∈ CandD2 b N)).card := by
  exact predicate_ncard_eq_box_filter b N (fun x => x ∈ CandD2 b N)
    (fun _ hx => hx.1)
#print axioms Paper7MomentCounts.candD2_ncard_eq_box

theorem canonD2_ncard_eq_box (b N : ℕ) :
    (canonD2 b N).ncard =
      (Finset.univ.filter (fun z : MomentBox b N => decodeBox z ∈ canonD2 b N)).card := by
  exact predicate_ncard_eq_box_filter b N (fun x => x ∈ canonD2 b N)
    (fun _ hx => hx.1.1)
#print axioms Paper7MomentCounts.canonD2_ncard_eq_box

/-- Equality here follows from the actual labelled definitions for even b.
No equality of the two canonical sets is asserted. -/
theorem candD2_eq_candB1_of_even (b N : ℕ) (hb : Even b) :
    CandD2 b N = CandB1 b N := by
  ext x
  change (Budget b N x ∧ Even b ∧ MomentPass false true false b N x) ↔
    (Budget b N x ∧ MomentPass false true false b N x)
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hb, h.2⟩⟩
#print axioms Paper7MomentCounts.candD2_eq_candB1_of_even

theorem candD2_ncard_eq_candB1_of_even (b N : ℕ) (hb : Even b) :
    (CandD2 b N).ncard = (CandB1 b N).ncard := by
  rw [candD2_eq_candB1_of_even b N hb]
#print axioms Paper7MomentCounts.candD2_ncard_eq_candB1_of_even

/-- All eight finite-set obligations, with their original separate set names.
The eight numerical-cardinality obligations remain separate. -/
theorem legacyMomentCounts_finite_components :
    (CandB1 4 41).Finite ∧ (canonB1 4 41).Finite ∧
    (CandD2 4 41).Finite ∧ (canonD2 4 41).Finite ∧
    (CandB1 6 42).Finite ∧ (canonB1 6 42).Finite ∧
    (CandD2 6 42).Finite ∧ (canonD2 6 42).Finite := by
  exact ⟨candB1_finite 4 41, canonB1_finite 4 41,
    candD2_finite 4 41, canonD2_finite 4 41,
    candB1_finite 6 42, canonB1_finite 6 42,
    candD2_finite 6 42, canonD2_finite 6 42⟩
#print axioms Paper7MomentCounts.legacyMomentCounts_finite_components

end Paper7MomentCounts
