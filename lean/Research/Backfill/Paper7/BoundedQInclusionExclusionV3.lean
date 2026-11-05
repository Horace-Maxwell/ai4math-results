import Mathlib

/-! UNCOMPILED candidate by /root/moment_b6_labelled_symbolic_2310.
Repair after actual851 FAILED (zero credit). Four shift-related helper types
are mathematically corrected, not claimed identical to the failed types.
Actual bounded-sum fibres, including empty dimension, are counted by finite
inclusion-exclusion. Unbounded residual fibres use the existing Sym stars-
and-bars equivalence and cardinality theorem. No numerical/coverage premise,
coefficient-cardinality premise, DP table, or candidate enumeration is used.
This NEW source has never been compiled or independently audited. The old
source and complete failed log are preserved. Only Mathlib is imported. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

abbrev BoundedIEWeakSum (n Q : ℕ) :=
  {q : Fin n → ℕ // ∑ i, q i = Q}
#print axioms Paper7MomentCounts.BoundedIEWeakSum

instance boundedIEWeakSumFintype (n Q : ℕ) : Fintype (BoundedIEWeakSum n Q) :=
  Fintype.ofEquiv (Sym (Fin n) Q) (Sym.equivNatSumOfFintype (Fin n) Q)
#print axioms Paper7MomentCounts.boundedIEWeakSumFintype

theorem boundedIEWeakSum_card (n Q : ℕ) :
    Nat.card (BoundedIEWeakSum n Q) = Nat.multichoose n Q := by
  calc
    Nat.card (BoundedIEWeakSum n Q) = Nat.card (Sym (Fin n) Q) :=
      Nat.card_congr (Sym.equivNatSumOfFintype (Fin n) Q).symm
    _ = Fintype.card (Sym (Fin n) Q) := Nat.card_eq_fintype_card
    _ = Nat.multichoose (Fintype.card (Fin n)) Q :=
      Sym.card_sym_eq_multichoose (Fin n) Q
    _ = Nat.multichoose n Q := by rw [Fintype.card_fin]
#print axioms Paper7MomentCounts.boundedIEWeakSum_card

theorem boundedIE_inf_filter {α ι : Type*} [Fintype α]
    (I : Finset ι) (p : ι → α → Prop) :
    I.inf (fun i => Finset.univ.filter (p i)) =
      Finset.univ.filter (fun x => ∀ i ∈ I, p i x) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    ext x
    simp
  | @insert i I _hi ih =>
    rw [Finset.inf_insert, ih]
    ext x
    simp
#print axioms Paper7MomentCounts.boundedIE_inf_filter

theorem boundedIE_finite_predicate_card {α ι : Type*} [Fintype α] [Fintype ι]
    (bad : ι → α → Prop) :
    (Nat.card {x : α // ∀ i, ¬ bad i x} : ℤ) =
      ∑ I : Finset ι, (-1 : ℤ) ^ I.card *
        (Nat.card {x : α // ∀ i ∈ I, bad i x} : ℤ) := by
  classical
  let S : ι → Finset α := fun i => Finset.univ.filter (bad i)
  have hgood : (Finset.univ : Finset ι).inf (fun i => (S i)ᶜ) =
      Finset.univ.filter (fun x => ∀ i, ¬ bad i x) := by
    ext x
    simp [Finset.mem_inf, S]
  have hbad (I : Finset ι) : I.inf S =
      Finset.univ.filter (fun x => ∀ i ∈ I, bad i x) := by
    ext x
    simp [Finset.mem_inf, S]
  have h := Finset.inclusion_exclusion_card_inf_compl (Finset.univ : Finset ι) S
  rw [hgood, Finset.powerset_univ] at h
  simp_rw [hbad] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h
#print axioms Paper7MomentCounts.boundedIE_finite_predicate_card

def boundedIELowerEquiv (n Q : ℕ) (s : Fin n → ℕ) (hs : (∑ i, s i) ≤ Q) :
    {q : BoundedIEWeakSum n Q // ∀ i, s i ≤ q.val i} ≃
      BoundedIEWeakSum n (Q - (∑ i, s i)) where
  toFun q := ⟨fun i => q.val.val i - s i, by
    rw [Finset.sum_tsub_distrib _ (fun i _ => q.property i), q.val.property]⟩
  invFun r := ⟨⟨fun i => r.val i + s i, by
    rw [Finset.sum_add_distrib, r.property]
    omega⟩, fun i => by
      change s i ≤ r.val i + s i
      omega⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact Nat.sub_add_cancel (q.property i)
  right_inv r := by
    apply Subtype.ext
    funext i
    exact Nat.add_sub_cancel (r.val i) (s i)
#print axioms Paper7MomentCounts.boundedIELowerEquiv

theorem boundedIELower_card (n Q : ℕ) (s : Fin n → ℕ) :
    Nat.card {q : BoundedIEWeakSum n Q // ∀ i, s i ≤ q.val i} =
      if (∑ i, s i) ≤ Q then Nat.multichoose n (Q - (∑ i, s i)) else 0 := by
  by_cases hs : (∑ i, s i) ≤ Q
  · rw [ite_eq_left hs]
    exact (Nat.card_congr (boundedIELowerEquiv n Q s hs)).trans
      (boundedIEWeakSum_card n (Q - (∑ i, s i)))
  · let : IsEmpty {q : BoundedIEWeakSum n Q // ∀ i, s i ≤ q.val i} := ⟨by
      intro q
      have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
        (fun i _ => q.property i)
      rw [q.val.property] at h
      exact hs h⟩
    rw [ite_eq_right hs, Nat.card_of_isEmpty]
#print axioms Paper7MomentCounts.boundedIELower_card

theorem boundedIEBad_card (n Q : ℕ) (z : Fin n → ℕ) (I : Finset (Fin n)) :
    Nat.card {q : BoundedIEWeakSum n Q // ∀ i ∈ I, z i < q.val i} =
      if (∑ i ∈ I, (z i + 1)) ≤ Q then
        Nat.multichoose n (Q - (∑ i ∈ I, (z i + 1))) else 0 := by
  let s : Fin n → ℕ := fun i => if i ∈ I then z i + 1 else 0
  have hsum : (∑ i, s i) = ∑ i ∈ I, (z i + 1) := by
    simp [s, Finset.sum_ite_mem]
  have hpred (q : BoundedIEWeakSum n Q) :
      (∀ i ∈ I, z i < q.val i) ↔ ∀ i, s i ≤ q.val i := by
    constructor
    · intro h i
      by_cases hi : i ∈ I
      · have hz := h i hi
        simp only [s, hi, ite_true]
        omega
      · simp [s, hi]
    · intro h i hi
      have hz : z i + 1 ≤ q.val i := by simpa only [s, hi, ite_true] using h i
      omega
  calc
    Nat.card {q : BoundedIEWeakSum n Q // ∀ i ∈ I, z i < q.val i} =
        Nat.card {q : BoundedIEWeakSum n Q // ∀ i, s i ≤ q.val i} :=
      Nat.card_congr (Equiv.subtypeEquivRight hpred)
    _ = if (∑ i, s i) ≤ Q then Nat.multichoose n (Q - (∑ i, s i)) else 0 :=
      boundedIELower_card n Q s
    _ = if (∑ i ∈ I, (z i + 1)) ≤ Q then
        Nat.multichoose n (Q - (∑ i ∈ I, (z i + 1))) else 0 := by rw [hsum]
#print axioms Paper7MomentCounts.boundedIEBad_card

def boundedIEBoundedEquiv (n Q : ℕ) (z : Fin n → ℕ) :
    {q : (i : Fin n) → Fin (z i + 1) // ∑ i, (q i).val = Q} ≃
      {q : BoundedIEWeakSum n Q // ∀ i, q.val i ≤ z i} where
  toFun q := ⟨⟨fun i => (q.val i).val, q.property⟩,
    fun i => Nat.le_of_lt_succ (q.val i).isLt⟩
  invFun q := ⟨fun i => ⟨q.val.val i, Nat.lt_succ_of_le (q.property i)⟩,
    q.val.property⟩
  left_inv q := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
#print axioms Paper7MomentCounts.boundedIEBoundedEquiv

theorem bounded_q_inclusion_exclusion (n Q : ℕ) (z : Fin n → ℕ) :
    (Nat.card {q : (i : Fin n) → Fin (z i + 1) // ∑ i, (q i).val = Q} : ℤ) =
      ∑ I : Finset (Fin n), (-1 : ℤ) ^ I.card *
        (if (∑ i ∈ I, (z i + 1)) ≤ Q then
          (Nat.multichoose n (Q - (∑ i ∈ I, (z i + 1))) : ℤ) else 0) := by
  calc
    (Nat.card {q : (i : Fin n) → Fin (z i + 1) // ∑ i, (q i).val = Q} : ℤ) =
        (Nat.card {q : BoundedIEWeakSum n Q // ∀ i, q.val i ≤ z i} : ℤ) :=
      congrArg (fun k : ℕ => (k : ℤ)) (Nat.card_congr (boundedIEBoundedEquiv n Q z))
    _ = ∑ I : Finset (Fin n), (-1 : ℤ) ^ I.card *
        (Nat.card {q : BoundedIEWeakSum n Q // ∀ i ∈ I, z i < q.val i} : ℤ) := by
      simpa only [not_lt] using
        (boundedIE_finite_predicate_card (fun (i : Fin n) (q : BoundedIEWeakSum n Q) =>
          z i < q.val i))
    _ = ∑ I : Finset (Fin n), (-1 : ℤ) ^ I.card *
        (if (∑ i ∈ I, (z i + 1)) ≤ Q then
          (Nat.multichoose n (Q - (∑ i ∈ I, (z i + 1))) : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro I _hI
      rw [boundedIEBad_card]
      by_cases h : (∑ i ∈ I, (z i + 1)) ≤ Q <;> simp [h]
#print axioms Paper7MomentCounts.bounded_q_inclusion_exclusion

theorem boundedIE_multichoose_succ (n m : ℕ) :
    Nat.multichoose (n+1) m = (m+n).choose n := by
  rw [Nat.multichoose_eq]
  have h : n+1+m-1 = m+n := by omega
  rw [h]
  exact Nat.choose_symm_add
#print axioms Paper7MomentCounts.boundedIE_multichoose_succ

theorem bounded_q_six_inclusion_exclusion_signed (z : Fin 6 → ℕ) (Q : ℕ) :
    (Nat.card {q : (i : Fin 6) → Fin (z i + 1) // ∑ i, (q i).val = Q} : ℤ) =
      ∑ I : Finset (Fin 6), (-1 : ℤ) ^ I.card *
        (let r : ℤ := (Q : ℤ) - ((∑ i ∈ I, (z i + 1) : ℕ) : ℤ)
         if r < 0 then 0 else (((r.toNat + 5).choose 5 : ℕ) : ℤ)) := by
  rw [bounded_q_inclusion_exclusion]
  apply Finset.sum_congr rfl
  intro I _hI
  apply congrArg (fun k : ℤ => (-1 : ℤ) ^ I.card * k)
  let d : ℕ := ∑ i ∈ I, (z i + 1)
  change (if d ≤ Q then (Nat.multichoose 6 (Q-d) : ℤ) else 0) =
    if (Q : ℤ) - d < 0 then 0 else
      (((((Q : ℤ) - d).toNat + 5).choose 5 : ℕ) : ℤ)
  by_cases hd : d ≤ Q
  · have hn : ¬ (Q : ℤ) - d < 0 := by omega
    have hr : (Q : ℤ) - d = ((Q-d : ℕ) : ℤ) := by omega
    simp only [hd, ite_true, hr, Int.toNat_natCast]
    exact_mod_cast boundedIE_multichoose_succ 5 (Q-d)
  · have hn : (Q : ℤ) - d < 0 := by omega
    simp only [hd, ite_false, hn, ite_true]
#print axioms Paper7MomentCounts.bounded_q_six_inclusion_exclusion_signed

theorem boundedIEShift_eq_sum_add_card (n : ℕ) (z : Fin n → ℕ) (I : Finset (Fin n)) :
    (∑ i ∈ I, (z i + 1)) = (∑ i ∈ I, z i) + I.card := by
  simp [Finset.sum_add_distrib]
#print axioms Paper7MomentCounts.boundedIEShift_eq_sum_add_card

theorem bounded_q_six_inclusion_exclusion_W6_form (z : Fin 6 → ℕ) (Q : ℕ) :
    (Nat.card {q : (i : Fin 6) → Fin (z i + 1) // ∑ i, (q i).val = Q} : ℤ) =
      ∑ I : Finset (Fin 6), (-1 : ℤ) ^ I.card *
        (let r : ℤ := (Q : ℤ) - (∑ i ∈ I, (z i : ℤ)) - I.card
         if r < 0 then 0 else (((r.toNat + 5).choose 5 : ℕ) : ℤ)) := by
  rw [bounded_q_six_inclusion_exclusion_signed]
  apply Finset.sum_congr rfl
  intro I _hI
  have hs : ((∑ i ∈ I, (z i + 1) : ℕ) : ℤ) =
      (∑ i ∈ I, (z i : ℤ)) + (I.card : ℤ) := by
    calc
      ((∑ i ∈ I, (z i + 1) : ℕ) : ℤ) =
          ((∑ i ∈ I, z i : ℕ) : ℤ) + (I.card : ℤ) := by
        rw [boundedIEShift_eq_sum_add_card, Nat.cast_add]
      _ = (∑ i ∈ I, (z i : ℤ)) + (I.card : ℤ) := by simp only [Nat.cast_sum]
  simp only [hs, sub_add_eq_sub_sub]
#print axioms Paper7MomentCounts.bounded_q_six_inclusion_exclusion_W6_form

theorem bounded_q_actual_card_zero_Q (n : ℕ) (z : Fin n → ℕ) :
    Nat.card {q : (i : Fin n) → Fin (z i + 1) // ∑ i, (q i).val = 0} = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨fun _ => 0, by simp⟩, ?_⟩
  intro q
  apply Subtype.ext
  funext i
  apply Fin.ext
  change (q.val i).val = 0
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => (q.val j).val) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [q.property] at h
  omega
#print axioms Paper7MomentCounts.bounded_q_actual_card_zero_Q

theorem bounded_q_actual_card_above_capacity (n Q : ℕ) (z : Fin n → ℕ)
    (hQ : (∑ i, z i) < Q) :
    Nat.card {q : (i : Fin n) → Fin (z i + 1) // ∑ i, (q i).val = Q} = 0 := by
  let : IsEmpty {q : (i : Fin n) → Fin (z i + 1) // ∑ i, (q i).val = Q} := ⟨by
    intro q
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
      (fun i _ => Nat.le_of_lt_succ (q.val i).isLt)
    rw [q.property] at h
    omega⟩
  exact Nat.card_of_isEmpty
#print axioms Paper7MomentCounts.bounded_q_actual_card_above_capacity

theorem bounded_q_actual_card_empty_dimension (Q : ℕ) (z : Fin 0 → ℕ) :
    Nat.card {q : (i : Fin 0) → Fin (z i + 1) // ∑ i, (q i).val = Q} =
      if Q = 0 then 1 else 0 := by
  by_cases hQ : Q = 0
  · subst Q
    rw [ite_eq_left (show (0 : ℕ) = 0 from rfl)]
    exact bounded_q_actual_card_zero_Q 0 z
  · rw [ite_eq_right hQ]
    exact bounded_q_actual_card_above_capacity 0 Q z (by
      simpa using Nat.pos_of_ne_zero hQ)
#print axioms Paper7MomentCounts.bounded_q_actual_card_empty_dimension

theorem bounded_q_actual_card_all_zero (n Q : ℕ) :
    Nat.card {q : (i : Fin n) → Fin ((0 : Fin n → ℕ) i + 1) //
      ∑ i, (q i).val = Q} = if Q = 0 then 1 else 0 := by
  by_cases hQ : Q = 0
  · subst Q
    rw [ite_eq_left (show (0 : ℕ) = 0 from rfl)]
    exact bounded_q_actual_card_zero_Q n 0
  · rw [ite_eq_right hQ]
    exact bounded_q_actual_card_above_capacity n Q 0 (by
      simpa using Nat.pos_of_ne_zero hQ)
#print axioms Paper7MomentCounts.bounded_q_actual_card_all_zero

end Paper7MomentCounts
