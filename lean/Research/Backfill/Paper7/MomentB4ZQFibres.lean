import Research.Backfill.Paper7.MomentBudgetEncoding
import Research.Backfill.Paper7.ZQBudgetCoordinates
import Research.Backfill.Paper7.BoundedQEmptyFibre

/-! Exact cardinality of the original labelled CandB1(4,41), decomposed by
z=p+q and the total Q. All zero-coordinate and zero-total boundaries remain
in the finite domain; only the original Budget excludes zero total weight.
The existential spectral feature is a predicate, never a counted witness. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7MomentDP Paper7Budget
open scoped BigOperators Classical

def b4Theta (z : Fin 4 → ℕ) (Q : ℕ) : ℤ :=
  8 + 3*((∑ i, z i : ℕ) : ℤ) + 2*(Q : ℤ) + ∑ i, (z i : ℤ)^2
#print axioms Paper7MomentCounts.b4Theta

def B4RowAccept (z : Fin 4 → ℕ) (Q : ℕ) : Prop :=
  (0 < (∑ i, z i) + Q ∧ 4 + ((∑ i, z i) + Q) ≤ 41) ∧
    ∃ a : Counts, evenFeatureCondition 4 41 ((∑ i, z i) + Q) Q (b4Theta z Q) a
#print axioms Paper7MomentCounts.B4RowAccept

abbrev B4RowIndex := BoundedTuple 4 37 × Fin 19
#print axioms Paper7MomentCounts.B4RowIndex

/-- q is kept as a natural-valued function so the index-dependent subtype
has an ordinary, explicit extensional equality on its underlying function. -/
abbrev B4IndexedRow (s : B4RowIndex) :=
  {q : Fin 4 → ℕ // (∀ i, q i ≤ s.1.val i) ∧
    (∑ i, q i) = s.2.val ∧ B4RowAccept s.1.val s.2.val}
#print axioms Paper7MomentCounts.B4IndexedRow

theorem b4_decode_mem_iff (z q : Fin 4 → ℕ) (hq : ∀ i, q i ≤ z i) :
    (fun i => z i - q i, q) ∈ CandB1 4 41 ↔ B4RowAccept z (∑ i, q i) := by
  exact zq_candB1_iff 4 41 (by decide) ⟨(z, q), hq⟩
#print axioms Paper7MomentCounts.b4_decode_mem_iff

theorem b4_encode_bounds (x : PQ 4) (hx : Budget 4 41 x) :
    (∑ i, (x.1 i + x.2 i)) ≤ 37 ∧ qSum x ≤ 18 := by
  have h := hx.2
  change 4 + (pSum x + 2*qSum x) ≤ 41 at h
  have hz : (∑ i, (x.1 i + x.2 i)) = pSum x + qSum x :=
    Finset.sum_add_distrib
  rw [hz]
  omega
#print axioms Paper7MomentCounts.b4_encode_bounds

theorem b4_encode_accept (x : PQ 4) (hx : x ∈ CandB1 4 41) :
    B4RowAccept (fun i => x.1 i + x.2 i) (qSum x) := by
  apply (b4_decode_mem_iff (fun i => x.1 i + x.2 i) x.2
    (fun i => Nat.le_add_left _ _)).mp
  simpa only [Nat.add_sub_cancel_right] using hx
#print axioms Paper7MomentCounts.b4_encode_accept

def b4Encode (x : {x : PQ 4 // x ∈ CandB1 4 41}) :
    Σ s : B4RowIndex, B4IndexedRow s :=
  ⟨(⟨fun i => x.val.1 i + x.val.2 i,
       (b4_encode_bounds x.val x.property.1).1⟩,
      ⟨qSum x.val, Nat.lt_succ_of_le (b4_encode_bounds x.val x.property.1).2⟩),
    ⟨x.val.2, (fun i => Nat.le_add_left (x.val.2 i) (x.val.1 i)), rfl,
      b4_encode_accept x.val x.property⟩⟩
#print axioms Paper7MomentCounts.b4Encode

def b4Decode (r : Σ s : B4RowIndex, B4IndexedRow s) :
    {x : PQ 4 // x ∈ CandB1 4 41} :=
  ⟨(fun i => r.1.1.val i - r.2.val i, r.2.val),
    (b4_decode_mem_iff r.1.1.val r.2.val r.2.property.1).mpr (by
      rw [r.2.property.2.1]
      exact r.2.property.2.2)⟩
#print axioms Paper7MomentCounts.b4Decode

theorem b4Decode_encode (x : {x : PQ 4 // x ∈ CandB1 4 41}) :
    b4Decode (b4Encode x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    exact Nat.add_sub_cancel_right _ _
  · rfl
#print axioms Paper7MomentCounts.b4Decode_encode

theorem b4Encode_decode (r : Σ s : B4RowIndex, B4IndexedRow s) :
    b4Encode (b4Decode r) = r := by
  apply Sigma.subtype_ext
  · apply Prod.ext
    · apply Subtype.ext
      funext i
      exact Nat.sub_add_cancel (r.2.property.1 i)
    · apply Fin.ext
      exact r.2.property.2.1
  · rfl
#print axioms Paper7MomentCounts.b4Encode_decode

def candB1B4ZQEquiv : {x : PQ 4 // x ∈ CandB1 4 41} ≃
    Σ s : B4RowIndex, B4IndexedRow s where
  toFun := b4Encode
  invFun := b4Decode
  left_inv := b4Decode_encode
  right_inv := b4Encode_decode
#print axioms Paper7MomentCounts.candB1B4ZQEquiv

instance b4IndexedRowFinite (s : B4RowIndex) : Finite (B4IndexedRow s) := by
  let f : B4IndexedRow s → BoundedQAssignment s.1.val :=
    fun q i => ⟨q.val i, Nat.lt_succ_of_le (q.property.1 i)⟩
  apply Finite.of_injective f
  intro q r h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)
#print axioms Paper7MomentCounts.b4IndexedRowFinite

def b4IndexedRowEquivFibre (s : B4RowIndex) (ha : B4RowAccept s.1.val s.2.val) :
    B4IndexedRow s ≃ BoundedQFibre s.1.val s.2.val where
  toFun q := ⟨(fun i => ⟨q.val i, Nat.lt_succ_of_le (q.property.1 i)⟩),
    q.property.2.1⟩
  invFun q := ⟨(fun i => (q.val i).val),
    (fun i => Nat.le_of_lt_succ (q.val i).isLt), q.property, ha⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
#print axioms Paper7MomentCounts.b4IndexedRowEquivFibre

theorem b4IndexedRow_card (s : B4RowIndex) :
    Nat.card (B4IndexedRow s) =
      if B4RowAccept s.1.val s.2.val then boundedQDP 4 s.1.val s.2.val else 0 := by
  by_cases ha : B4RowAccept s.1.val s.2.val
  · rw [ite_eq_left ha, boundedQDP_eq_card]
    exact Nat.card_congr (b4IndexedRowEquivFibre s ha)
  · let : IsEmpty (B4IndexedRow s) := ⟨fun q => ha q.property.2.2⟩
    rw [ite_eq_right ha]
    exact Nat.card_of_isEmpty
#print axioms Paper7MomentCounts.b4IndexedRow_card

/-- The complete original labelled set is counted, once per z and Q. This is
an unevaluated exact finite sum, not the numerical equality 410544. -/
theorem candB1_b4_ncard_eq_zq_sum :
    (CandB1 4 41).ncard = ∑ z : BoundedTuple 4 37, ∑ Q : Fin 19,
      if B4RowAccept z.val Q.val then boundedQDP 4 z.val Q.val else 0 := by
  change Nat.card {x : PQ 4 // x ∈ CandB1 4 41} = _
  calc
    Nat.card {x : PQ 4 // x ∈ CandB1 4 41} =
        Nat.card (Σ s : B4RowIndex, B4IndexedRow s) := Nat.card_congr candB1B4ZQEquiv
    _ = ∑ s : B4RowIndex, Nat.card (B4IndexedRow s) := Nat.card_sigma
    _ = ∑ s : B4RowIndex,
        if B4RowAccept s.1.val s.2.val then boundedQDP 4 s.1.val s.2.val else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      exact b4IndexedRow_card s
    _ = _ := by
      exact Finset.sum_finset_product
        (Finset.univ : Finset B4RowIndex)
        (Finset.univ : Finset (BoundedTuple 4 37))
        (fun _ : BoundedTuple 4 37 => (Finset.univ : Finset (Fin 19)))
        (by intro s; simp only [Finset.mem_univ, and_self])
        (f := fun s : B4RowIndex =>
          if B4RowAccept s.1.val s.2.val then boundedQDP 4 s.1.val s.2.val else 0)
#print axioms Paper7MomentCounts.candB1_b4_ncard_eq_zq_sum

def B4GuardedRowAccept (z : Fin 4 → ℕ) (Q : ℕ) : Prop :=
  Q ≤ (∑ i, z i) ∧ B4RowAccept z Q
#print axioms Paper7MomentCounts.B4GuardedRowAccept

theorem b4_insert_total_guard (z : Fin 4 → ℕ) (Q : ℕ) :
    (if B4RowAccept z Q then boundedQDP 4 z Q else 0) =
      if B4GuardedRowAccept z Q then boundedQDP 4 z Q else 0 := by
  by_cases hQ : Q ≤ ∑ i, z i
  · simp only [B4GuardedRowAccept, hQ, true_and]
  · have hz := boundedQDP_eq_zero_of_total_lt z Q (Nat.lt_of_not_ge hQ)
    simp only [B4GuardedRowAccept, hQ, false_and, hz, ite_self]
#print axioms Paper7MomentCounts.b4_insert_total_guard

theorem candB1_b4_ncard_eq_guarded_zq_sum :
    (CandB1 4 41).ncard = ∑ z : BoundedTuple 4 37, ∑ Q : Fin 19,
      if B4GuardedRowAccept z.val Q.val then boundedQDP 4 z.val Q.val else 0 := by
  rw [candB1_b4_ncard_eq_zq_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro Q _
  exact b4_insert_total_guard z.val Q.val
#print axioms Paper7MomentCounts.candB1_b4_ncard_eq_guarded_zq_sum

end Paper7MomentCounts
