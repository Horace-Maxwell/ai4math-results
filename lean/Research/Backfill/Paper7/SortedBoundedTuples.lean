import Research.Backfill.Paper7.BudgetTupleCounts

/-! Source-only candidate. Sorting all bounded tuples, including zero budgets,
empty tuples and repeated entries. No representative count or table is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7SortedRows
open Paper7Budget
open scoped BigOperators Classical

def permute {n B : ℕ} (e : Equiv.Perm (Fin n))
    (x : BoundedTuple n B) : BoundedTuple n B :=
  ⟨x.val ∘ e, by
    change (∑ i, x.val (e i)) ≤ B
    rw [e.bijective.sum_comp x.val]
    exact x.property⟩
#print axioms Paper7SortedRows.permute

theorem permute_refl {n B : ℕ} (x : BoundedTuple n B) :
    permute (Equiv.refl _) x = x := by
  apply Subtype.ext
  rfl
#print axioms Paper7SortedRows.permute_refl

/-- Inverse precomposition makes this a genuine left symmetric-group action. -/
instance boundedTuplePermAction (n B : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (BoundedTuple n B) where
  smul e x := permute e.symm x
  one_smul x := by
    apply Subtype.ext
    rfl
  mul_smul e f x := by
    apply Subtype.ext
    rfl
#print axioms Paper7SortedRows.boundedTuplePermAction

abbrev SortedTuple (n B : ℕ) := {x : BoundedTuple n B // Monotone x.val}
#print axioms Paper7SortedRows.SortedTuple

def sortBounded {n B : ℕ} (x : BoundedTuple n B) : SortedTuple n B :=
  ⟨permute (Tuple.sort x.val) x, Tuple.monotone_sort x.val⟩
#print axioms Paper7SortedRows.sortBounded

theorem sortBounded_of_sorted {n B : ℕ} (r : SortedTuple n B) :
    sortBounded r.val = r := by
  apply Subtype.ext
  apply Subtype.ext
  change r.val.val ∘ Tuple.sort r.val.val = r.val.val
  rw [Tuple.sort_eq_refl_iff_monotone.mpr r.property]
  rfl
#print axioms Paper7SortedRows.sortBounded_of_sorted

theorem sortBounded_permute {n B : ℕ} (e : Equiv.Perm (Fin n))
    (x : BoundedTuple n B) : sortBounded (permute e x) = sortBounded x := by
  apply Subtype.ext
  apply Subtype.ext
  change (x.val ∘ e) ∘ Tuple.sort (x.val ∘ e) = x.val ∘ Tuple.sort x.val
  exact Tuple.comp_perm_comp_sort_eq_comp_sort
#print axioms Paper7SortedRows.sortBounded_permute

/-- Each orbit has one and only one sorted bounded tuple. The sorting
permutation itself need not be unique when coordinates coincide. -/
theorem existsUnique_sorted_representative {n B : ℕ} (x : BoundedTuple n B) :
    ∃! r : SortedTuple n B, ∃ e : Equiv.Perm (Fin n), r.val = permute e x := by
  refine ⟨sortBounded x, ⟨Tuple.sort x.val, rfl⟩, ?_⟩
  intro r hr
  rcases hr with ⟨e, he⟩
  calc
    r = sortBounded r.val := (sortBounded_of_sorted r).symm
    _ = sortBounded (permute e x) := congrArg sortBounded he
    _ = sortBounded x := sortBounded_permute e x
#print axioms Paper7SortedRows.existsUnique_sorted_representative

theorem sort_eq_iff_permutation {n B : ℕ} (x y : BoundedTuple n B) :
    sortBounded x = sortBounded y ↔
      ∃ e : Equiv.Perm (Fin n), y = permute e x := by
  constructor
  · intro h
    have hv : x.val ∘ Tuple.sort x.val = y.val ∘ Tuple.sort y.val :=
      congrArg (fun r : SortedTuple n B => r.val.val) h
    refine ⟨(Tuple.sort y.val).symm.trans (Tuple.sort x.val), ?_⟩
    apply Subtype.ext
    funext i
    have hi := congrFun hv ((Tuple.sort y.val).symm i)
    change y.val i = x.val (Tuple.sort x.val ((Tuple.sort y.val).symm i))
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi.symm
  · rintro ⟨e, rfl⟩
    exact (sortBounded_permute e x).symm
#print axioms Paper7SortedRows.sort_eq_iff_permutation

end Paper7SortedRows
