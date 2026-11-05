import Research.Backfill.Paper7.MomentB6TripleCapacityCardV2
import Research.Backfill.Paper7.BoundedQInclusionExclusionV3

/-! UNCOMPILED general-Q bridge by /root/moment_b6_labelled_symbolic_2310.
The actual bounded-q inclusion-exclusion parent is successful actual858.
The capacity-card V2 parent is a separately pending repair unless a later
producer receipt establishes success. All capacities, statistics and Q are
arbitrary naturals. No cardinality/coverage/numerical premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

def labelledTripleVector (u : ℕ × ℕ × ℕ) : Fin 3 → ℕ :=
  ![u.1, u.2.1, u.2.2]
#print axioms Paper7MomentCounts.labelledTripleVector

abbrev labelledTripleQFiber (u : ℕ × ℕ × ℕ) (Q : ℕ) :=
  {q : Fin (u.1+1) × Fin (u.2.1+1) × Fin (u.2.2+1) //
    q.1.val + q.2.1.val + q.2.2.val = Q}
#print axioms Paper7MomentCounts.labelledTripleQFiber

def labelledTripleQFunctionEquiv (u : ℕ × ℕ × ℕ) (Q : ℕ) :
    {q : (i : Fin 3) → Fin (labelledTripleVector u i + 1) //
      (∑ i, (q i).val) = Q} ≃ labelledTripleQFiber u Q where
  toFun q := ⟨(q.val 0, q.val 1, q.val 2), by
    simpa only [Fin.sum_univ_three] using q.property⟩
  invFun q := ⟨fun i =>
    ⟨![q.val.1.val, q.val.2.1.val, q.val.2.2.val] i, by
      fin_cases i
      · exact q.val.1.isLt
      · exact q.val.2.1.isLt
      · exact q.val.2.2.isLt⟩, by
    simpa [Fin.sum_univ_three] using q.property⟩
  left_inv q := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    fin_cases i <;> rfl
  right_inv q := by
    apply Subtype.ext
    rfl
#print axioms Paper7MomentCounts.labelledTripleQFunctionEquiv

def labelledTripleQSwapFirstEquiv (c a b Q : ℕ) :
    labelledTripleQFiber (c,a,b) Q ≃ labelledTripleQFiber (a,c,b) Q where
  toFun q := ⟨(q.val.2.1, q.val.1, q.val.2.2), by
    change q.val.2.1.val + q.val.1.val + q.val.2.2.val = Q
    have h := q.property
    omega⟩
  invFun q := ⟨(q.val.2.1, q.val.1, q.val.2.2), by
    change q.val.2.1.val + q.val.1.val + q.val.2.2.val = Q
    have h := q.property
    omega⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl
#print axioms Paper7MomentCounts.labelledTripleQSwapFirstEquiv

def labelledTripleQSwapLastEquiv (c a b Q : ℕ) :
    labelledTripleQFiber (c,a,b) Q ≃ labelledTripleQFiber (c,b,a) Q where
  toFun q := ⟨(q.val.1, q.val.2.2, q.val.2.1), by
    change q.val.1.val + q.val.2.2.val + q.val.2.1.val = Q
    have h := q.property
    omega⟩
  invFun q := ⟨(q.val.1, q.val.2.2, q.val.2.1), by
    change q.val.1.val + q.val.2.2.val + q.val.2.1.val = Q
    have h := q.property
    omega⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl
#print axioms Paper7MomentCounts.labelledTripleQSwapLastEquiv

theorem labelledTripleQFiber_card_orbit (c a b Q : ℕ) (u : ℕ × ℕ × ℕ)
    (hu : u ∈ labelledTripleOrbit c a b) :
    Nat.card (labelledTripleQFiber u Q) = Nat.card (labelledTripleQFiber (c,a,b) Q) := by
  have hf (x y z : ℕ) := Nat.card_congr (labelledTripleQSwapFirstEquiv x y z Q)
  have hl (x y z : ℕ) := Nat.card_congr (labelledTripleQSwapLastEquiv x y z Q)
  simp only [labelledTripleOrbit, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact hl c b a
  · exact hf a c b
  · exact (hl a b c).trans (hf a c b)
  · exact (hf b c a).trans (hl c b a)
  · exact (hf b a c).trans ((hl a b c).trans (hf a c b))
#print axioms Paper7MomentCounts.labelledTripleQFiber_card_orbit

def labelledOrderedTripleQEquiv (A B Q : ℕ) :
    {x : (Fin 3 → ℕ) × (Fin 3 → ℕ) //
      (∀ i, x.2 i ≤ x.1 i) ∧ (∑ i, x.1 i) = A ∧
        (∑ i, x.1 i^2) = B ∧ (∑ i, x.2 i) = Q} ≃
      Σ u : ↥(labelledTripleCapacityRealization A B), labelledTripleQFiber u.val Q where
  toFun x := ⟨⟨(x.val.1 0, x.val.1 1, x.val.1 2), by
    apply (labelledTripleCapacityRealization_mem_iff A B _).mpr
    simpa only [Fin.sum_univ_three] using
      And.intro x.property.2.1 x.property.2.2.1⟩,
    ⟨(⟨x.val.2 0, Nat.lt_succ_of_le (x.property.1 0)⟩,
       ⟨x.val.2 1, Nat.lt_succ_of_le (x.property.1 1)⟩,
       ⟨x.val.2 2, Nat.lt_succ_of_le (x.property.1 2)⟩), by
      simpa only [Fin.sum_univ_three] using x.property.2.2.2⟩⟩
  invFun y := ⟨(labelledTripleVector y.1.val,
    ![y.2.val.1.val, y.2.val.2.1.val, y.2.val.2.2.val]), by
    have hc := (labelledTripleCapacityRealization_mem_iff A B y.1.val).mp y.1.property
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact Nat.le_of_lt_succ y.2.val.1.isLt
      · exact Nat.le_of_lt_succ y.2.val.2.1.isLt
      · exact Nat.le_of_lt_succ y.2.val.2.2.isLt
    · simpa [labelledTripleVector, Fin.sum_univ_three] using hc.1
    · simpa [labelledTripleVector, Fin.sum_univ_three] using hc.2
    · simpa [Fin.sum_univ_three] using y.2.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  right_inv y := by
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · apply heq_of_eq
      apply Subtype.ext
      rfl
#print axioms Paper7MomentCounts.labelledOrderedTripleQEquiv

theorem labelledExactCapacityQCard_three_eq_actual_fibres (A B Q : ℕ) :
    labelledExactCapacityQCard 3 A B Q =
      ∑ c ∈ labelledTripleScalarRange A B,
        if B6SortedTripleDiscriminantAccept A B c then
          labelledSortedTripleMultiplicity c (labelledTripleHigh A B c) (labelledTripleLow A B c) *
            Nat.card (labelledTripleQFiber
              (c, labelledTripleHigh A B c, labelledTripleLow A B c) Q) else 0 := by
  unfold labelledExactCapacityQCard
  calc
    Nat.card {x : (Fin 3 → ℕ) × (Fin 3 → ℕ) //
      (∀ i, x.2 i ≤ x.1 i) ∧ (∑ i, x.1 i) = A ∧
        (∑ i, x.1 i^2) = B ∧ (∑ i, x.2 i) = Q} =
        Nat.card (Σ u : ↥(labelledTripleCapacityRealization A B), labelledTripleQFiber u.val Q) :=
      Nat.card_congr (labelledOrderedTripleQEquiv A B Q)
    _ = ∑ u : ↥(labelledTripleCapacityRealization A B), Nat.card (labelledTripleQFiber u.val Q) :=
      Nat.card_sigma
    _ = ∑ u ∈ labelledTripleCapacityRealization A B, Nat.card (labelledTripleQFiber u Q) :=
      Finset.sum_coe_sort (labelledTripleCapacityRealization A B)
        (fun u : ℕ × ℕ × ℕ => Nat.card (labelledTripleQFiber u Q))
    _ = ∑ c ∈ labelledTripleCapacitySupport A B,
        ∑ u ∈ labelledTripleOrbit c (labelledTripleHigh A B c) (labelledTripleLow A B c),
          Nat.card (labelledTripleQFiber u Q) := by
      unfold labelledTripleCapacityRealization
      exact Finset.sum_biUnion (labelledTripleCapacity_orbits_disjoint A B)
    _ = ∑ c ∈ labelledTripleCapacitySupport A B,
        labelledSortedTripleMultiplicity c (labelledTripleHigh A B c) (labelledTripleLow A B c) *
          Nat.card (labelledTripleQFiber
            (c, labelledTripleHigh A B c, labelledTripleLow A B c) Q) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hg : B6SortedTripleDiscriminantAccept A B c := (Finset.mem_filter.mp hc).2
      have hs := labelled_sorted_triple_decode_sound A B c hg
      have hconst := Finset.sum_const_nat (fun u hu =>
        labelledTripleQFiber_card_orbit c (labelledTripleHigh A B c)
          (labelledTripleLow A B c) Q u hu)
      rw [hconst, labelledTripleOrbit_card c (labelledTripleHigh A B c)
        (labelledTripleLow A B c) hs.1 hs.2.1]
    _ = ∑ c ∈ labelledTripleScalarRange A B,
        if B6SortedTripleDiscriminantAccept A B c then
          labelledSortedTripleMultiplicity c (labelledTripleHigh A B c) (labelledTripleLow A B c) *
            Nat.card (labelledTripleQFiber
              (c, labelledTripleHigh A B c, labelledTripleLow A B c) Q) else 0 := by
      simp only [labelledTripleCapacitySupport, Finset.sum_filter]
#print axioms Paper7MomentCounts.labelledExactCapacityQCard_three_eq_actual_fibres

def labelledTripleSubsetTerm (z : Fin 3 → ℕ) (Q : ℕ) (I : Finset (Fin 3)) : ℤ :=
  (-1 : ℤ)^I.card * labelledPositiveTriangular
    ((Q : ℤ) - ((∑ i ∈ I, (z i + 1) : ℕ) : ℤ))
#print axioms Paper7MomentCounts.labelledTripleSubsetTerm

theorem labelledTripleBoundedFunction_card_signed (z : Fin 3 → ℕ) (Q : ℕ) :
    (Nat.card {q : (i : Fin 3) → Fin (z i+1) // (∑ i, (q i).val) = Q} : ℤ) =
      ∑ I : Finset (Fin 3), labelledTripleSubsetTerm z Q I := by
  rw [bounded_q_inclusion_exclusion]
  apply Finset.sum_congr rfl
  intro I _hI
  unfold labelledTripleSubsetTerm
  apply congrArg (fun k : ℤ => (-1 : ℤ)^I.card * k)
  let d : ℕ := ∑ i ∈ I, (z i+1)
  change (if d ≤ Q then (Nat.multichoose 3 (Q-d) : ℤ) else 0) =
    labelledPositiveTriangular ((Q : ℤ) - d)
  unfold labelledPositiveTriangular
  by_cases hd : d ≤ Q
  · have hr : (Q : ℤ) - d = ((Q-d : ℕ) : ℤ) := by omega
    simp only [hd, ite_true, hr, Int.toNat_natCast]
    exact_mod_cast boundedIE_multichoose_succ 2 (Q-d)
  · have hn : (Q : ℤ) - d < 0 := by omega
    simp only [hd, ite_false, hn, ite_true]
#print axioms Paper7MomentCounts.labelledTripleBoundedFunction_card_signed

theorem labelled_sum_finset_fin3 (F : Finset (Fin 3) → ℤ) :
    (∑ I : Finset (Fin 3), F I) =
      F ∅ + F {0} + F {1} + F {2} + F {0,1} + F {0,2} + F {1,2} + F {0,1,2} := by
  classical
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by
    ext i
    fin_cases i <;> simp
  have hp : ({2} : Finset (Fin 3)).powerset = {∅, {2}} := by
    change (insert (2 : Fin 3) (∅ : Finset (Fin 3))).powerset = _
    rw [Finset.powerset_insert]
    simp
  rw [← Finset.powerset_univ, hu]
  simp [Finset.sum_powerset_insert, hp, add_assoc, add_left_comm, add_comm]
#print axioms Paper7MomentCounts.labelled_sum_finset_fin3

theorem labelledTripleSubsetTerm_empty (z : Fin 3 → ℕ) (Q : ℕ) :
    labelledTripleSubsetTerm z Q ∅ = labelledPositiveTriangular Q := by
  simp [labelledTripleSubsetTerm]
#print axioms Paper7MomentCounts.labelledTripleSubsetTerm_empty

theorem labelledTripleSubsetTerm_singleton (z : Fin 3 → ℕ) (Q : ℕ) (i : Fin 3) :
    labelledTripleSubsetTerm z Q {i} = -labelledPositiveTriangular ((Q : ℤ) - z i - 1) := by
  unfold labelledTripleSubsetTerm
  simp only [Finset.card_singleton, Finset.sum_singleton, pow_one, neg_one_mul]
  congr 1
  congr 1
  push_cast
  ring
#print axioms Paper7MomentCounts.labelledTripleSubsetTerm_singleton

theorem labelledTripleSubsetTerm_pair (z : Fin 3 → ℕ) (Q : ℕ) (i j : Fin 3) (hij : i ≠ j) :
    labelledTripleSubsetTerm z Q {i,j} =
      labelledPositiveTriangular ((Q : ℤ) - z i - z j - 2) := by
  have hc : ({i,j} : Finset (Fin 3)).card = 2 := by simp [hij]
  have hs : (∑ k ∈ ({i,j} : Finset (Fin 3)), (z k+1)) = (z i+1)+(z j+1) := by
    simp [hij]
  unfold labelledTripleSubsetTerm
  rw [hc, hs]
  simp only [show (-1 : ℤ)^2 = 1 by norm_num, one_mul]
  congr 1
  push_cast
  ring
#print axioms Paper7MomentCounts.labelledTripleSubsetTerm_pair

theorem labelledTripleSubsetTerm_three (z : Fin 3 → ℕ) (Q : ℕ)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    labelledTripleSubsetTerm z Q {i,j,k} =
      -labelledPositiveTriangular ((Q : ℤ) - z i - z j - z k - 3) := by
  have hc : ({i,j,k} : Finset (Fin 3)).card = 3 := by simp [hij, hik, hjk]
  have hs : (∑ l ∈ ({i,j,k} : Finset (Fin 3)), (z l+1)) =
      (z i+1)+((z j+1)+(z k+1)) := by
    simp [hij, hik, hjk]
  unfold labelledTripleSubsetTerm
  rw [hc, hs]
  simp only [show (-1 : ℤ)^3 = -1 by norm_num, neg_one_mul]
  congr 1
  congr 1
  push_cast
  ring
#print axioms Paper7MomentCounts.labelledTripleSubsetTerm_three

theorem labelledTripleSubsetSum_eq_weight (z : Fin 3 → ℕ) (Q : ℕ) :
    (∑ I : Finset (Fin 3), labelledTripleSubsetTerm z Q I) =
      labelledTripleQWeight (z 0) (z 1) (z 2) Q := by
  rw [labelled_sum_finset_fin3, labelledTripleSubsetTerm_empty,
    labelledTripleSubsetTerm_singleton z Q 0,
    labelledTripleSubsetTerm_singleton z Q 1,
    labelledTripleSubsetTerm_singleton z Q 2,
    labelledTripleSubsetTerm_pair z Q 0 1 (by norm_num),
    labelledTripleSubsetTerm_pair z Q 0 2 (by norm_num),
    labelledTripleSubsetTerm_pair z Q 1 2 (by norm_num),
    labelledTripleSubsetTerm_three z Q 0 1 2 (by norm_num) (by norm_num) (by norm_num)]
  unfold labelledTripleQWeight
  ring
#print axioms Paper7MomentCounts.labelledTripleSubsetSum_eq_weight

theorem labelledTripleQFiber_card_eq_weight (u : ℕ × ℕ × ℕ) (Q : ℕ) :
    (Nat.card (labelledTripleQFiber u Q) : ℤ) = labelledTripleQWeight u.1 u.2.1 u.2.2 Q := by
  calc
    (Nat.card (labelledTripleQFiber u Q) : ℤ) =
        (Nat.card {q : (i : Fin 3) → Fin (labelledTripleVector u i+1) //
          (∑ i, (q i).val) = Q} : ℤ) :=
      congrArg (fun k : ℕ => (k : ℤ)) (Nat.card_congr (labelledTripleQFunctionEquiv u Q).symm)
    _ = ∑ I : Finset (Fin 3), labelledTripleSubsetTerm (labelledTripleVector u) Q I :=
      labelledTripleBoundedFunction_card_signed (labelledTripleVector u) Q
    _ = labelledTripleQWeight u.1 u.2.1 u.2.2 Q :=
      labelledTripleSubsetSum_eq_weight (labelledTripleVector u) Q
#print axioms Paper7MomentCounts.labelledTripleQFiber_card_eq_weight

theorem labelledTripleDiscriminantKernel_eq_actual (A B Q : ℕ) :
    labelledTripleDiscriminantKernel A B Q = (labelledExactCapacityQCard 3 A B Q : ℤ) := by
  rw [labelledExactCapacityQCard_three_eq_actual_fibres]
  unfold labelledTripleDiscriminantKernel
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hg : B6SortedTripleDiscriminantAccept A B c
  · rw [ite_eq_left hg, ite_eq_left hg, Nat.cast_mul]
    exact congrArg (fun k : ℤ =>
      (labelledSortedTripleMultiplicity c
        (labelledTripleHigh A B c) (labelledTripleLow A B c) : ℤ) * k)
      (labelledTripleQFiber_card_eq_weight
        (c, labelledTripleHigh A B c, labelledTripleLow A B c) Q).symm
  · rw [ite_eq_right hg, ite_eq_right hg, Nat.cast_zero]
#print axioms Paper7MomentCounts.labelledTripleDiscriminantKernel_eq_actual

end Paper7MomentCounts
