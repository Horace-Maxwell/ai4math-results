import Research.Backfill.Paper7.BudgetTupleCounts

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
This module has not been compiled or accepted. It decomposes the genuine bounded
tuple domain by its first coordinate, including every zero and endpoint case.
No list enumeration, certificate data, or numerical count is assumed.
-/
set_option autoImplicit false
noncomputable section

namespace Paper7Budget

open scoped BigOperators

theorem boundedTuple_head_le (n B : ℕ) (x : BoundedTuple (n + 1) B) :
    x.val 0 ≤ B := by
  have hx := x.property
  rw [Fin.sum_univ_succ] at hx
  omega

#print axioms Paper7Budget.boundedTuple_head_le

theorem boundedTuple_tail_le (n B : ℕ) (x : BoundedTuple (n + 1) B) :
    (∑ i : Fin n, Fin.tail x.val i) ≤ B - x.val 0 := by
  have hx := x.property
  rw [Fin.sum_univ_succ] at hx
  change (∑ i : Fin n, x.val i.succ) ≤ B - x.val 0
  omega

#print axioms Paper7Budget.boundedTuple_tail_le

/-- Reattach a head coordinate using exactly its remaining budget. -/
def boundedTupleCons (n B : ℕ) (a : Fin (B + 1))
    (t : BoundedTuple n (B - a.val)) : BoundedTuple (n + 1) B :=
  ⟨Fin.cons (α := fun _ : Fin (n + 1) => ℕ) a.val t.val, by
    rw [Fin.sum_cons]
    have ha : a.val ≤ B := Nat.le_of_lt_succ a.isLt
    have ht := t.property
    omega⟩

#print axioms Paper7Budget.boundedTupleCons

/-- Every bounded tuple has exactly one head and exactly one bounded tail. -/
def boundedTupleHeadEquiv (n B : ℕ) :
    BoundedTuple (n + 1) B ≃
      Σ a : Fin (B + 1), BoundedTuple n (B - a.val) where
  toFun x :=
    ⟨⟨x.val 0, Nat.lt_succ_of_le (boundedTuple_head_le n B x)⟩,
      ⟨Fin.tail (α := fun _ : Fin (n + 1) => ℕ) x.val,
        boundedTuple_tail_le n B x⟩⟩
  invFun s := boundedTupleCons n B s.1 s.2
  left_inv x := by
    apply Subtype.ext
    exact Fin.cons_self_tail (α := fun _ : Fin (n + 1) => ℕ) x.val
  right_inv s := by
    apply Sigma.subtype_ext
    · apply Fin.ext
      rfl
    · exact Fin.tail_cons (α := fun _ : Fin (n + 1) => ℕ) s.1.val s.2.val

#print axioms Paper7Budget.boundedTupleHeadEquiv

/-- Exact head decomposition of a finite sum; no numerical evaluation occurs. -/
theorem sum_boundedTuple_head {M : Type*} [AddCommMonoid M] (n B : ℕ)
    (f : BoundedTuple (n + 1) B → M) :
    (∑ x : BoundedTuple (n + 1) B, f x) =
      ∑ a : Fin (B + 1), ∑ t : BoundedTuple n (B - a.val),
        f (boundedTupleCons n B a t) := by
  calc
    (∑ x : BoundedTuple (n + 1) B, f x) =
        ∑ s : (Σ a : Fin (B + 1), BoundedTuple n (B - a.val)),
          f ((boundedTupleHeadEquiv n B).symm s) :=
      ((boundedTupleHeadEquiv n B).symm.sum_comp f).symm
    _ = _ := Fintype.sum_sigma
      (fun s : (Σ a : Fin (B + 1), BoundedTuple n (B - a.val)) =>
        f (boundedTupleCons n B s.1 s.2))

#print axioms Paper7Budget.sum_boundedTuple_head

/-- A one-coordinate tuple corresponding to the full inclusive range 0 through B. -/
def boundedTupleOne (B : ℕ) (a : Fin (B + 1)) : BoundedTuple 1 B :=
  ⟨fun _ => a.val, by
    simpa only [Fin.sum_univ_one] using Nat.le_of_lt_succ a.isLt⟩

#print axioms Paper7Budget.boundedTupleOne

def boundedTupleOneEquivFin (B : ℕ) : BoundedTuple 1 B ≃ Fin (B + 1) where
  toFun x := ⟨x.val 0, Nat.lt_succ_of_le (boundedTuple_head_le 0 B x)⟩
  invFun := boundedTupleOne B
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (Subsingleton.elim (0 : Fin 1) i)
  right_inv a := by
    apply Fin.ext
    rfl

#print axioms Paper7Budget.boundedTupleOneEquivFin

theorem sum_boundedTuple_one {M : Type*} [AddCommMonoid M] (B : ℕ)
    (f : BoundedTuple 1 B → M) :
    (∑ x : BoundedTuple 1 B, f x) =
      ∑ a : Fin (B + 1), f (boundedTupleOne B a) :=
  ((boundedTupleOneEquivFin B).symm.sum_comp f).symm

#print axioms Paper7Budget.sum_boundedTuple_one

/-- Zero budget forces every coordinate to be zero, including the empty tuple case. -/
theorem boundedTuple_zeroBudget_eq (n : ℕ) (x : BoundedTuple n 0) :
    x.val = fun _ => 0 := by
  funext i
  have hi : x.val i ≤ ∑ j, x.val j :=
    Finset.single_le_sum (f := x.val)
      (fun j _ => Nat.zero_le (x.val j)) (Finset.mem_univ i)
  have hx := x.property
  omega

#print axioms Paper7Budget.boundedTuple_zeroBudget_eq

end Paper7Budget
