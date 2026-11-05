import Mathlib

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
This module has not been compiled or accepted. Assignments have their actual
coordinate-dependent bounds. The recursion removes the last coordinate, so a
prefix table processed in the order z0,z1,... agrees with the stated recurrence.
No numerical layer, candidate-generator result, or final moment count is assumed.
-/
set_option autoImplicit false
noncomputable section

namespace Paper7MomentDP

open scoped BigOperators Classical

abbrev BoundedQAssignment {n : ℕ} (z : Fin n → ℕ) :=
  (i : Fin n) → Fin (z i + 1)

#print axioms Paper7MomentDP.BoundedQAssignment

def boundedQSum {n : ℕ} (z : Fin n → ℕ) (q : BoundedQAssignment z) : ℕ :=
  ∑ i, (q i).val

#print axioms Paper7MomentDP.boundedQSum

abbrev BoundedQFibre {n : ℕ} (z : Fin n → ℕ) (Q : ℕ) :=
  {q : BoundedQAssignment z // boundedQSum z q = Q}

#print axioms Paper7MomentDP.BoundedQFibre

def boundedQFibreCard {n : ℕ} (z : Fin n → ℕ) (Q : ℕ) : ℕ :=
  Nat.card (BoundedQFibre z Q)

#print axioms Paper7MomentDP.boundedQFibreCard

theorem boundedQSum_cons (n : ℕ) (z : Fin (n + 1) → ℕ)
    (a : Fin (z 0 + 1)) (q : BoundedQAssignment (Fin.tail z)) :
    boundedQSum z (Fin.cons a q) = a.val + boundedQSum (Fin.tail z) q := by
  exact Fin.sum_univ_succ (fun i : Fin (n + 1) =>
    (Fin.cons (α := fun j : Fin (n + 1) => Fin (z j + 1)) a q i).val)

#print axioms Paper7MomentDP.boundedQSum_cons

theorem boundedQSum_head_tail (n : ℕ) (z : Fin (n + 1) → ℕ)
    (q : BoundedQAssignment z) :
    boundedQSum z q = (q 0).val + boundedQSum (Fin.tail z) (Fin.tail q) :=
  Fin.sum_univ_succ (fun i => (q i).val)

#print axioms Paper7MomentDP.boundedQSum_head_tail

theorem boundedQSum_snoc (n : ℕ) (z : Fin (n + 1) → ℕ)
    (q : BoundedQAssignment (Fin.init z)) (a : Fin (z (Fin.last n) + 1)) :
    boundedQSum z (Fin.snoc q a) = a.val + boundedQSum (Fin.init z) q := by
  calc
    boundedQSum z (Fin.snoc q a) = boundedQSum (Fin.init z) q + a.val := by
      simp only [boundedQSum, Fin.sum_univ_castSucc]
      apply congrArg₂ Nat.add
      · apply Finset.sum_congr rfl
        intro i _
        exact congrArg Fin.val
          (Fin.snoc_castSucc (α := fun j : Fin (n + 1) => Fin (z j + 1)) a q i)
      · exact congrArg Fin.val
          (Fin.snoc_last (α := fun j : Fin (n + 1) => Fin (z j + 1)) a q)
    _ = a.val + boundedQSum (Fin.init z) q := Nat.add_comm _ _

#print axioms Paper7MomentDP.boundedQSum_snoc

theorem boundedQSum_init_last (n : ℕ) (z : Fin (n + 1) → ℕ)
    (q : BoundedQAssignment z) :
    boundedQSum z q = (q (Fin.last n)).val + boundedQSum (Fin.init z) (Fin.init q) := by
  calc
    boundedQSum z q = boundedQSum (Fin.init z) (Fin.init q) + (q (Fin.last n)).val :=
      Fin.sum_univ_castSucc (fun i => (q i).val)
    _ = (q (Fin.last n)).val + boundedQSum (Fin.init z) (Fin.init q) := Nat.add_comm _ _

#print axioms Paper7MomentDP.boundedQSum_init_last

/-- Exact first-coordinate decomposition, without truncated subtraction. -/
def boundedQFibreHeadEquiv (n : ℕ) (z : Fin (n + 1) → ℕ) (Q : ℕ) :
    BoundedQFibre z Q ≃
      Σ a : Fin (z 0 + 1),
        {q : BoundedQAssignment (Fin.tail z) // a.val + boundedQSum (Fin.tail z) q = Q} where
  toFun q := ⟨q.val 0, Fin.tail q.val,
    (boundedQSum_head_tail n z q.val).symm.trans q.property⟩
  invFun q := ⟨Fin.cons q.1 q.2.val,
    (boundedQSum_cons n z q.1 q.2.val).trans q.2.property⟩
  left_inv q := by
    apply Subtype.ext
    exact Fin.cons_self_tail q.val
  right_inv q := by
    rcases q with ⟨a, q, hq⟩
    apply Sigma.subtype_ext rfl
    funext i
    rfl

#print axioms Paper7MomentDP.boundedQFibreHeadEquiv

/-- Exact last-coordinate decomposition used by prefix-layer certificates. -/
def boundedQFibreSnocEquiv (n : ℕ) (z : Fin (n + 1) → ℕ) (Q : ℕ) :
    BoundedQFibre z Q ≃
      Σ a : Fin (z (Fin.last n) + 1),
        {q : BoundedQAssignment (Fin.init z) // a.val + boundedQSum (Fin.init z) q = Q} where
  toFun q := ⟨q.val (Fin.last n), Fin.init q.val,
    (boundedQSum_init_last n z q.val).symm.trans q.property⟩
  invFun q := ⟨Fin.snoc q.2.val q.1,
    (boundedQSum_snoc n z q.2.val q.1).trans q.2.property⟩
  left_inv q := by
    apply Subtype.ext
    exact Fin.snoc_init_self q.val
  right_inv q := by
    rcases q with ⟨a, q, hq⟩
    apply Sigma.subtype_ext
    · exact Fin.snoc_last (α := fun i : Fin (n + 1) => Fin (z i + 1)) a q
    · exact Fin.init_snoc (α := fun i : Fin (n + 1) => Fin (z i + 1)) a q

#print axioms Paper7MomentDP.boundedQFibreSnocEquiv

/-- A residual fibre is empty when the chosen coordinate already exceeds the target. -/
theorem boundedQResidual_card {n : ℕ} (z : Fin n → ℕ) (a Q : ℕ) :
    Nat.card {q : BoundedQAssignment z // a + boundedQSum z q = Q} =
      if a ≤ Q then boundedQFibreCard z (Q - a) else 0 := by
  by_cases ha : a ≤ Q
  · simp only [ha, ite_true]
    unfold boundedQFibreCard
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun q => by
      omega))
  · let : IsEmpty {q : BoundedQAssignment z // a + boundedQSum z q = Q} :=
      ⟨by
        rintro ⟨q, hq⟩
        omega⟩
    simp only [ha, ite_false, Nat.card_of_isEmpty]

#print axioms Paper7MomentDP.boundedQResidual_card

theorem boundedQFibreCard_zero (z : Fin 0 → ℕ) (Q : ℕ) :
    boundedQFibreCard z Q = if Q = 0 then 1 else 0 := by
  by_cases hQ : Q = 0
  · subst Q
    change Nat.card (BoundedQFibre z 0) = 1
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨fun i => Fin.elim0 i, ?_⟩, ?_⟩
    · simp [boundedQSum]
    · intro q
      apply Subtype.ext
      funext i
      exact Fin.elim0 i
  · let : IsEmpty (BoundedQFibre z Q) :=
      ⟨by
        intro q
        apply hQ
        calc
          Q = boundedQSum z q.val := q.property.symm
          _ = 0 := by simp [boundedQSum]⟩
    change Nat.card (BoundedQFibre z Q) = if Q = 0 then 1 else 0
    simp only [hQ, ite_false, Nat.card_of_isEmpty]

#print axioms Paper7MomentDP.boundedQFibreCard_zero

theorem boundedQFibreCard_head (n : ℕ) (z : Fin (n + 1) → ℕ) (Q : ℕ) :
    boundedQFibreCard z Q =
      ∑ a : Fin (z 0 + 1),
        if a.val ≤ Q then boundedQFibreCard (Fin.tail z) (Q - a.val) else 0 := by
  calc
    boundedQFibreCard z Q = Nat.card
        (Σ a : Fin (z 0 + 1),
          {q : BoundedQAssignment (Fin.tail z) // a.val + boundedQSum (Fin.tail z) q = Q}) :=
      Nat.card_congr (boundedQFibreHeadEquiv n z Q)
    _ = ∑ a : Fin (z 0 + 1),
        Nat.card {q : BoundedQAssignment (Fin.tail z) //
          a.val + boundedQSum (Fin.tail z) q = Q} := Nat.card_sigma
    _ = ∑ a : Fin (z 0 + 1),
        if a.val ≤ Q then boundedQFibreCard (Fin.tail z) (Q - a.val) else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact boundedQResidual_card (Fin.tail z) a.val Q

#print axioms Paper7MomentDP.boundedQFibreCard_head

theorem boundedQFibreCard_snoc (n : ℕ) (z : Fin (n + 1) → ℕ) (Q : ℕ) :
    boundedQFibreCard z Q =
      ∑ a : Fin (z (Fin.last n) + 1),
        if a.val ≤ Q then boundedQFibreCard (Fin.init z) (Q - a.val) else 0 := by
  calc
    boundedQFibreCard z Q = Nat.card
        (Σ a : Fin (z (Fin.last n) + 1),
          {q : BoundedQAssignment (Fin.init z) // a.val + boundedQSum (Fin.init z) q = Q}) :=
      Nat.card_congr (boundedQFibreSnocEquiv n z Q)
    _ = ∑ a : Fin (z (Fin.last n) + 1),
        Nat.card {q : BoundedQAssignment (Fin.init z) //
          a.val + boundedQSum (Fin.init z) q = Q} := Nat.card_sigma
    _ = ∑ a : Fin (z (Fin.last n) + 1),
        if a.val ≤ Q then boundedQFibreCard (Fin.init z) (Q - a.val) else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact boundedQResidual_card (Fin.init z) a.val Q

#print axioms Paper7MomentDP.boundedQFibreCard_snoc

/-- Prefix-oriented DP: append the last bound to the preceding prefix. -/
def boundedQDP : (n : ℕ) → (Fin n → ℕ) → ℕ → ℕ
  | 0, _z, Q => if Q = 0 then 1 else 0
  | n + 1, z, Q => ∑ a : Fin (z (Fin.last n) + 1),
      if a.val ≤ Q then boundedQDP n (Fin.init z) (Q - a.val) else 0

#print axioms Paper7MomentDP.boundedQDP

theorem boundedQDP_zero (z : Fin 0 → ℕ) (Q : ℕ) :
    boundedQDP 0 z Q = if Q = 0 then 1 else 0 := rfl

#print axioms Paper7MomentDP.boundedQDP_zero

theorem boundedQDP_snoc (n : ℕ) (z : Fin (n + 1) → ℕ) (Q : ℕ) :
    boundedQDP (n + 1) z Q =
      ∑ a : Fin (z (Fin.last n) + 1),
        if a.val ≤ Q then boundedQDP n (Fin.init z) (Q - a.val) else 0 := rfl

#print axioms Paper7MomentDP.boundedQDP_snoc

/-- Every DP value counts exactly the genuine bounded-sum fibre. -/
theorem boundedQDP_eq_card (n : ℕ) :
    ∀ (z : Fin n → ℕ) (Q : ℕ), boundedQDP n z Q = boundedQFibreCard z Q := by
  induction n with
  | zero =>
    intro z Q
    exact (boundedQFibreCard_zero z Q).symm
  | succ n ih =>
    intro z Q
    rw [boundedQDP_snoc, boundedQFibreCard_snoc]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases ha : a.val ≤ Q
    · simp only [ha, ite_true]
      exact ih (Fin.init z) (Q - a.val)
    · simp only [ha, ite_false]

#print axioms Paper7MomentDP.boundedQDP_eq_card

/-- Direct interface for the actual PQ-to-bounded-q fibre equivalence. -/
theorem boundedQDP_eq_fibre_card (n : ℕ) (z : Fin n → ℕ) (Q : ℕ) :
    boundedQDP n z Q =
      Nat.card {q : (i : Fin n) → Fin (z i + 1) // ∑ i, (q i).val = Q} :=
  boundedQDP_eq_card n z Q

#print axioms Paper7MomentDP.boundedQDP_eq_fibre_card

/-- The head recurrence follows from the same true cardinality; it does not reorder prefix layers. -/
theorem boundedQDP_head (n : ℕ) (z : Fin (n + 1) → ℕ) (Q : ℕ) :
    boundedQDP (n + 1) z Q =
      ∑ a : Fin (z 0 + 1),
        if a.val ≤ Q then boundedQDP n (Fin.tail z) (Q - a.val) else 0 := by
  calc
    boundedQDP (n + 1) z Q = boundedQFibreCard z Q := boundedQDP_eq_card (n + 1) z Q
    _ = ∑ a : Fin (z 0 + 1),
        if a.val ≤ Q then boundedQFibreCard (Fin.tail z) (Q - a.val) else 0 :=
      boundedQFibreCard_head n z Q
    _ = ∑ a : Fin (z 0 + 1),
        if a.val ≤ Q then boundedQDP n (Fin.tail z) (Q - a.val) else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases ha : a.val ≤ Q
      · simp only [ha, ite_true]
        exact (boundedQDP_eq_card n (Fin.tail z) (Q - a.val)).symm
      · simp only [ha, ite_false]

#print axioms Paper7MomentDP.boundedQDP_head

end Paper7MomentDP
