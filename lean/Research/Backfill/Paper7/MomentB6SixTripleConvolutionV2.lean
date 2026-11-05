import Research.Backfill.Paper7.MomentB6TripleGeneralQV3

/-! Source-only actual six-coordinate fibre convolution.
The imported general-Q V3 source is the actual872 successful object; it is reused without recompilation.
No numerical values, cardinality premises or coverage premises are introduced. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

abbrev labelledCapacityQFibre (n A B Q : ℕ) :=
  {x : (Fin n → ℕ) × (Fin n → ℕ) //
    (∀ i, x.2 i ≤ x.1 i) ∧ (∑ i, x.1 i) = A ∧
      (∑ i, x.1 i^2) = B ∧ (∑ i, x.2 i) = Q}
#print axioms Paper7MomentCounts.labelledCapacityQFibre

instance labelledCapacityQFibre_three_finite (A B Q : ℕ) :
    Finite (labelledCapacityQFibre 3 A B Q) :=
  Finite.of_equiv _ (labelledOrderedTripleQEquiv A B Q).symm
#print axioms Paper7MomentCounts.labelledCapacityQFibre_three_finite

def labelledSixFront (f : Fin 6 → ℕ) : Fin 3 → ℕ := fun i => f (Fin.castAdd 3 i)
#print axioms Paper7MomentCounts.labelledSixFront

def labelledSixBack (f : Fin 6 → ℕ) : Fin 3 → ℕ := fun i => f (Fin.natAdd 3 i)
#print axioms Paper7MomentCounts.labelledSixBack

def labelledSixJoin (f g : Fin 3 → ℕ) : Fin 6 → ℕ :=
  fun i => Fin.addCases (m := 3) (n := 3) (motive := fun _ : Fin (3+3) => ℕ) f g i
#print axioms Paper7MomentCounts.labelledSixJoin

theorem labelledSix_front_join (f g : Fin 3 → ℕ) :
    labelledSixFront (labelledSixJoin f g) = f := by
  funext i
  exact Fin.addCases_left (m := 3) (n := 3)
    (motive := fun _ : Fin (3+3) => ℕ) (left := f) (right := g) i
#print axioms Paper7MomentCounts.labelledSix_front_join

theorem labelledSix_back_join (f g : Fin 3 → ℕ) :
    labelledSixBack (labelledSixJoin f g) = g := by
  funext i
  exact Fin.addCases_right (m := 3) (n := 3)
    (motive := fun _ : Fin (3+3) => ℕ) (left := f) (right := g) i
#print axioms Paper7MomentCounts.labelledSix_back_join

theorem labelledSix_join_front_back (f : Fin 6 → ℕ) :
    labelledSixJoin (labelledSixFront f) (labelledSixBack f) = f := by
  funext i
  exact Fin.addCases_castAdd_natAdd (m := 3) (n := 3)
    (γ := fun _ : Fin (3+3) => ℕ) f i
#print axioms Paper7MomentCounts.labelledSix_join_front_back

theorem labelledSix_sum_split (f : Fin 6 → ℕ) :
    (∑ i, f i) = (∑ i, labelledSixFront f i) + ∑ i, labelledSixBack f i :=
  Fin.sum_univ_add (a := 3) (b := 3) f
#print axioms Paper7MomentCounts.labelledSix_sum_split

theorem labelledSix_square_sum_split (f : Fin 6 → ℕ) :
    (∑ i, f i^2) = (∑ i, labelledSixFront f i^2) + ∑ i, labelledSixBack f i^2 :=
  Fin.sum_univ_add (a := 3) (b := 3) (fun i => f i^2)
#print axioms Paper7MomentCounts.labelledSix_square_sum_split

theorem labelledSix_sum_join (f g : Fin 3 → ℕ) :
    (∑ i, labelledSixJoin f g i) = (∑ i, f i) + ∑ i, g i := by
  rw [labelledSix_sum_split, labelledSix_front_join, labelledSix_back_join]
#print axioms Paper7MomentCounts.labelledSix_sum_join

theorem labelledSix_square_sum_join (f g : Fin 3 → ℕ) :
    (∑ i, labelledSixJoin f g i^2) = (∑ i, f i^2) + ∑ i, g i^2 := by
  rw [labelledSix_square_sum_split, labelledSix_front_join, labelledSix_back_join]
#print axioms Paper7MomentCounts.labelledSix_square_sum_join

abbrev labelledSixSplitIndex (Z R Q : ℕ) := Fin (Z+1) × Fin (R+1) × Fin (Q+1)
#print axioms Paper7MomentCounts.labelledSixSplitIndex

abbrev labelledSixTriplePair (Z R Q : ℕ) :=
  Σ r : labelledSixSplitIndex Z R Q,
    labelledCapacityQFibre 3 r.1.val r.2.1.val r.2.2.val ×
      labelledCapacityQFibre 3 (Z-r.1.val) (R-r.2.1.val) (Q-r.2.2.val)
#print axioms Paper7MomentCounts.labelledSixTriplePair

def labelledSixTripleJoin (Z R Q : ℕ) :
    labelledSixTriplePair Z R Q → labelledCapacityQFibre 6 Z R Q := fun y =>
  ⟨(labelledSixJoin y.2.1.val.1 y.2.2.val.1,
     labelledSixJoin y.2.1.val.2 y.2.2.val.2), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (m := 3) (n := 3)
        (motive := fun j : Fin (3+3) =>
          labelledSixJoin y.2.1.val.2 y.2.2.val.2 j ≤
            labelledSixJoin y.2.1.val.1 y.2.2.val.1 j)
        (fun j => ?_) (fun j => ?_) i
      · simpa only [labelledSixJoin, Fin.addCases_left] using y.2.1.property.1 j
      · simpa only [labelledSixJoin, Fin.addCases_right] using y.2.2.property.1 j
    · rw [labelledSix_sum_join, y.2.1.property.2.1, y.2.2.property.2.1]
      have h := y.1.1.isLt
      omega
    · rw [labelledSix_square_sum_join, y.2.1.property.2.2.1, y.2.2.property.2.2.1]
      have h := y.1.2.1.isLt
      omega
    · rw [labelledSix_sum_join, y.2.1.property.2.2.2, y.2.2.property.2.2.2]
      have h := y.1.2.2.isLt
      omega⟩
#print axioms Paper7MomentCounts.labelledSixTripleJoin

theorem labelledSixTripleJoin_injective (Z R Q : ℕ) :
    Function.Injective (labelledSixTripleJoin Z R Q) := by
  rintro ⟨r, x, y⟩ ⟨s, u, v⟩ h
  have hz : labelledSixJoin x.val.1 y.val.1 = labelledSixJoin u.val.1 v.val.1 :=
    congrArg (fun w : labelledCapacityQFibre 6 Z R Q => w.val.1) h
  have hq : labelledSixJoin x.val.2 y.val.2 = labelledSixJoin u.val.2 v.val.2 :=
    congrArg (fun w : labelledCapacityQFibre 6 Z R Q => w.val.2) h
  have hlz : x.val.1 = u.val.1 := by
    simpa only [labelledSix_front_join] using congrArg labelledSixFront hz
  have hrz : y.val.1 = v.val.1 := by
    simpa only [labelledSix_back_join] using congrArg labelledSixBack hz
  have hlq : x.val.2 = u.val.2 := by
    simpa only [labelledSix_front_join] using congrArg labelledSixFront hq
  have hrq : y.val.2 = v.val.2 := by
    simpa only [labelledSix_back_join] using congrArg labelledSixBack hq
  have hrs : r = s := by
    apply Prod.ext
    · apply Fin.ext
      calc
        r.1.val = ∑ i, x.val.1 i := x.property.2.1.symm
        _ = ∑ i, u.val.1 i := congrArg (fun f : Fin 3 → ℕ => ∑ i, f i) hlz
        _ = s.1.val := u.property.2.1
    · apply Prod.ext
      · apply Fin.ext
        calc
          r.2.1.val = ∑ i, x.val.1 i^2 := x.property.2.2.1.symm
          _ = ∑ i, u.val.1 i^2 := congrArg (fun f : Fin 3 → ℕ => ∑ i, f i^2) hlz
          _ = s.2.1.val := u.property.2.2.1
      · apply Fin.ext
        calc
          r.2.2.val = ∑ i, x.val.2 i := x.property.2.2.2.symm
          _ = ∑ i, u.val.2 i := congrArg (fun f : Fin 3 → ℕ => ∑ i, f i) hlq
          _ = s.2.2.val := u.property.2.2.2
  cases hrs
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    exact Prod.ext (Subtype.ext (Prod.ext hlz hlq)) (Subtype.ext (Prod.ext hrz hrq))
#print axioms Paper7MomentCounts.labelledSixTripleJoin_injective

theorem labelledSixTripleJoin_surjective (Z R Q : ℕ) :
    Function.Surjective (labelledSixTripleJoin Z R Q) := by
  intro x
  have hz := labelledSix_sum_split x.val.1
  have hr := labelledSix_square_sum_split x.val.1
  have hq := labelledSix_sum_split x.val.2
  rw [x.property.2.1] at hz
  rw [x.property.2.2.1] at hr
  rw [x.property.2.2.2] at hq
  let r : labelledSixSplitIndex Z R Q :=
    (⟨∑ i, labelledSixFront x.val.1 i, by omega⟩,
     ⟨∑ i, labelledSixFront x.val.1 i^2, by omega⟩,
     ⟨∑ i, labelledSixFront x.val.2 i, by omega⟩)
  let l : labelledCapacityQFibre 3 r.1.val r.2.1.val r.2.2.val :=
    ⟨(labelledSixFront x.val.1, labelledSixFront x.val.2),
      ⟨fun i => x.property.1 (Fin.castAdd 3 i), rfl, rfl, rfl⟩⟩
  let v : labelledCapacityQFibre 3 (Z-r.1.val) (R-r.2.1.val) (Q-r.2.2.val) :=
    ⟨(labelledSixBack x.val.1, labelledSixBack x.val.2), by
      refine ⟨fun i => x.property.1 (Fin.natAdd 3 i), ?_, ?_, ?_⟩
      · change (∑ i, labelledSixBack x.val.1 i) = Z - (∑ i, labelledSixFront x.val.1 i)
        omega
      · change (∑ i, labelledSixBack x.val.1 i^2) = R - (∑ i, labelledSixFront x.val.1 i^2)
        omega
      · change (∑ i, labelledSixBack x.val.2 i) = Q - (∑ i, labelledSixFront x.val.2 i)
        omega⟩
  refine ⟨⟨r, l, v⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact labelledSix_join_front_back x.val.1
  · exact labelledSix_join_front_back x.val.2
#print axioms Paper7MomentCounts.labelledSixTripleJoin_surjective

def labelledSixTripleEquiv (Z R Q : ℕ) :
    labelledCapacityQFibre 6 Z R Q ≃ labelledSixTriplePair Z R Q :=
  (Equiv.ofBijective (labelledSixTripleJoin Z R Q)
    ⟨labelledSixTripleJoin_injective Z R Q, labelledSixTripleJoin_surjective Z R Q⟩).symm
#print axioms Paper7MomentCounts.labelledSixTripleEquiv

theorem labelledExactCapacityQCard_six_convolution (Z R Q : ℕ) :
    labelledExactCapacityQCard 6 Z R Q =
      ∑ A ∈ Finset.range (Z+1), ∑ B ∈ Finset.range (R+1), ∑ t ∈ Finset.range (Q+1),
        labelledExactCapacityQCard 3 A B t *
          labelledExactCapacityQCard 3 (Z-A) (R-B) (Q-t) := by
  unfold labelledExactCapacityQCard
  rw [Nat.card_congr (labelledSixTripleEquiv Z R Q), Nat.card_sigma]
  simp only [Nat.card_prod, Fintype.sum_prod_type]
  change (∑ a : Fin (Z+1), ∑ b : Fin (R+1), ∑ t : Fin (Q+1),
    labelledExactCapacityQCard 3 a.val b.val t.val *
      labelledExactCapacityQCard 3 (Z-a.val) (R-b.val) (Q-t.val)) = _
  rw [Fin.sum_univ_eq_sum_range (fun A : ℕ =>
    ∑ b : Fin (R+1), ∑ t : Fin (Q+1),
      labelledExactCapacityQCard 3 A b.val t.val *
        labelledExactCapacityQCard 3 (Z-A) (R-b.val) (Q-t.val)) (Z+1)]
  apply Finset.sum_congr rfl
  intro A _hA
  rw [Fin.sum_univ_eq_sum_range (fun B : ℕ =>
    ∑ t : Fin (Q+1), labelledExactCapacityQCard 3 A B t.val *
      labelledExactCapacityQCard 3 (Z-A) (R-B) (Q-t.val)) (R+1)]
  apply Finset.sum_congr rfl
  intro B _hB
  exact Fin.sum_univ_eq_sum_range (fun t : ℕ =>
    labelledExactCapacityQCard 3 A B t *
      labelledExactCapacityQCard 3 (Z-A) (R-B) (Q-t)) (Q+1)
#print axioms Paper7MomentCounts.labelledExactCapacityQCard_six_convolution

theorem labelledExactCapacityQCard_six_kernel_convolution (Z R Q : ℕ) :
    (labelledExactCapacityQCard 6 Z R Q : ℤ) =
      ∑ A ∈ Finset.range (Z+1), ∑ B ∈ Finset.range (R+1), ∑ t ∈ Finset.range (Q+1),
        labelledTripleDiscriminantKernel A B t *
          labelledTripleDiscriminantKernel (Z-A) (R-B) (Q-t) := by
  rw [labelledExactCapacityQCard_six_convolution]
  simp only [Nat.cast_sum, Nat.cast_mul, ← labelledTripleDiscriminantKernel_eq_actual]
#print axioms Paper7MomentCounts.labelledExactCapacityQCard_six_kernel_convolution

theorem labelledCapacityQFibre_q_le (n A B Q : ℕ) (x : labelledCapacityQFibre n A B Q) :
    Q ≤ A := by
  calc
    Q = ∑ i, x.val.2 i := x.property.2.2.2.symm
    _ ≤ ∑ i, x.val.1 i := Finset.sum_le_sum (fun i _hi => x.property.1 i)
    _ = A := x.property.2.1
#print axioms Paper7MomentCounts.labelledCapacityQFibre_q_le

theorem labelledExactCapacityQCard_zero_of_q_gt (n A B Q : ℕ) (h : A < Q) :
    labelledExactCapacityQCard n A B Q = 0 := by
  let : IsEmpty (labelledCapacityQFibre n A B Q) :=
    ⟨fun x => (not_le_of_gt h) (labelledCapacityQFibre_q_le n A B Q x)⟩
  exact Nat.card_of_isEmpty
#print axioms Paper7MomentCounts.labelledExactCapacityQCard_zero_of_q_gt

theorem labelledTripleDiscriminantKernel_zero_of_q_gt (A B Q : ℕ) (h : A < Q) :
    labelledTripleDiscriminantKernel A B Q = 0 := by
  rw [labelledTripleDiscriminantKernel_eq_actual,
    labelledExactCapacityQCard_zero_of_q_gt 3 A B Q h, Nat.cast_zero]
#print axioms Paper7MomentCounts.labelledTripleDiscriminantKernel_zero_of_q_gt

theorem labelledTripleKernel_q_split_range (Z R A B Q : ℕ) :
    (∑ t ∈ Finset.range (Q+1), labelledTripleDiscriminantKernel A B t *
      labelledTripleDiscriminantKernel (Z-A) (R-B) (Q-t)) =
    ∑ t ∈ labelledTripleQSplitRange Z A Q, labelledTripleDiscriminantKernel A B t *
      labelledTripleDiscriminantKernel (Z-A) (R-B) (Q-t) := by
  symm
  apply Finset.sum_subset
  · intro t ht
    have h := (Finset.mem_Icc.mp ht).2
    apply Finset.mem_range.mpr
    omega
  · intro t ht hn
    have htQ : t ≤ Q := by have h := Finset.mem_range.mp ht; omega
    by_cases htA : t ≤ A
    · have hsmall : Z-A < Q-t := by
        change t ∉ Finset.Icc (Q-(Z-A)) (min Q A) at hn
        simp only [Finset.mem_Icc] at hn
        omega
      rw [labelledTripleDiscriminantKernel_zero_of_q_gt (Z-A) (R-B) (Q-t) hsmall,
        mul_zero]
    · have hlarge : A < t := by omega
      rw [labelledTripleDiscriminantKernel_zero_of_q_gt A B t hlarge, zero_mul]
#print axioms Paper7MomentCounts.labelledTripleKernel_q_split_range

theorem labelledExactCapacityQCard_six_kernel_q_pruned (Z R Q : ℕ) :
    (labelledExactCapacityQCard 6 Z R Q : ℤ) =
      ∑ A ∈ Finset.range (Z+1), ∑ B ∈ Finset.range (R+1),
        ∑ t ∈ labelledTripleQSplitRange Z A Q,
          labelledTripleDiscriminantKernel A B t *
            labelledTripleDiscriminantKernel (Z-A) (R-B) (Q-t) := by
  rw [labelledExactCapacityQCard_six_kernel_convolution]
  apply Finset.sum_congr rfl
  intro A _hA
  apply Finset.sum_congr rfl
  intro B _hB
  exact labelledTripleKernel_q_split_range Z R A B Q
#print axioms Paper7MomentCounts.labelledExactCapacityQCard_six_kernel_q_pruned

theorem labelledCapacityQFibre_square_sum_le (n A B Q : ℕ)
    (x : labelledCapacityQFibre n A B Q) : B ≤ A^2 := by
  have hcoord (i : Fin n) : x.val.1 i ≤ A := by
    calc
      x.val.1 i ≤ ∑ j, x.val.1 j :=
        Finset.single_le_sum (fun j _hj => Nat.zero_le (x.val.1 j)) (Finset.mem_univ i)
      _ = A := x.property.2.1
  calc
    B = ∑ i, x.val.1 i^2 := x.property.2.2.1.symm
    _ ≤ ∑ i, x.val.1 i * A := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa only [pow_two] using Nat.mul_le_mul_left (x.val.1 i) (hcoord i)
    _ = (∑ i, x.val.1 i) * A := (Finset.sum_mul _ _ _).symm
    _ = A^2 := by rw [x.property.2.1, pow_two]
#print axioms Paper7MomentCounts.labelledCapacityQFibre_square_sum_le

theorem labelledCapacityQFibre_triple_statistic_guard (A B Q : ℕ)
    (x : labelledCapacityQFibre 3 A B Q) : B6TripleStatisticGuard A B := by
  have ha : x.val.1 0 + x.val.1 1 + x.val.1 2 = A := by
    simpa only [Fin.sum_univ_three] using x.property.2.1
  have hb : x.val.1 0^2 + x.val.1 1^2 + x.val.1 2^2 = B := by
    simpa only [Fin.sum_univ_three] using x.property.2.2.1
  have haI : (x.val.1 0 : ℤ) + x.val.1 1 + x.val.1 2 = A := by exact_mod_cast ha
  have hbI : (x.val.1 0 : ℤ)^2 + (x.val.1 1 : ℤ)^2 + (x.val.1 2 : ℤ)^2 = B := by
    exact_mod_cast hb
  have hcI : (A : ℤ)^2 ≤ 3*(B : ℤ) := by
    nlinarith [sq_nonneg ((x.val.1 0 : ℤ) - x.val.1 1),
      sq_nonneg ((x.val.1 0 : ℤ) - x.val.1 2),
      sq_nonneg ((x.val.1 1 : ℤ) - x.val.1 2)]
  have hp (k : ℕ) : k^2 % 2 = k % 2 := by
    rw [Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [h]
    · rw [h]
  refine ⟨?_, labelledCapacityQFibre_square_sum_le 3 A B Q x, ?_⟩
  · exact_mod_cast hcI
  · calc
      B % 2 = (x.val.1 0^2 + x.val.1 1^2 + x.val.1 2^2) % 2 :=
        congrArg (fun k : ℕ => k % 2) hb.symm
      _ = (x.val.1 0 + x.val.1 1 + x.val.1 2) % 2 := by
        rw [Nat.add_mod (x.val.1 0^2 + x.val.1 1^2) (x.val.1 2^2) 2,
          Nat.add_mod (x.val.1 0^2) (x.val.1 1^2) 2,
          hp (x.val.1 0), hp (x.val.1 1), hp (x.val.1 2),
          Nat.add_mod (x.val.1 0 + x.val.1 1) (x.val.1 2) 2,
          Nat.add_mod (x.val.1 0) (x.val.1 1) 2]
      _ = A % 2 := congrArg (fun k : ℕ => k % 2) ha
#print axioms Paper7MomentCounts.labelledCapacityQFibre_triple_statistic_guard

theorem labelledTripleDiscriminantKernel_zero_of_bad_statistics (A B Q : ℕ)
    (h : ¬ B6TripleStatisticGuard A B) : labelledTripleDiscriminantKernel A B Q = 0 := by
  let : IsEmpty (labelledCapacityQFibre 3 A B Q) :=
    ⟨fun x => h (labelledCapacityQFibre_triple_statistic_guard A B Q x)⟩
  rw [labelledTripleDiscriminantKernel_eq_actual]
  have he : labelledExactCapacityQCard 3 A B Q = 0 := Nat.card_of_isEmpty
  rw [he, Nat.cast_zero]
#print axioms Paper7MomentCounts.labelledTripleDiscriminantKernel_zero_of_bad_statistics

theorem labelledExactCapacityQCard_six_kernel_statistic_pruned (Z R Q : ℕ) :
    (labelledExactCapacityQCard 6 Z R Q : ℤ) =
      ∑ A ∈ Finset.range (Z+1), ∑ B ∈ Finset.range (R+1),
        if B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B) then
          ∑ t ∈ labelledTripleQSplitRange Z A Q,
            labelledTripleDiscriminantKernel A B t *
              labelledTripleDiscriminantKernel (Z-A) (R-B) (Q-t)
        else 0 := by
  rw [labelledExactCapacityQCard_six_kernel_q_pruned]
  apply Finset.sum_congr rfl
  intro A _hA
  apply Finset.sum_congr rfl
  intro B _hB
  by_cases hg : B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B)
  · rw [ite_eq_left hg]
  · rw [ite_eq_right hg]
    apply Finset.sum_eq_zero
    intro t _ht
    by_cases hl : B6TripleStatisticGuard A B
    · have hr : ¬ B6TripleStatisticGuard (Z-A) (R-B) := fun h => hg ⟨hl,h⟩
      rw [labelledTripleDiscriminantKernel_zero_of_bad_statistics (Z-A) (R-B) (Q-t) hr,
        mul_zero]
    · rw [labelledTripleDiscriminantKernel_zero_of_bad_statistics A B t hl, zero_mul]
#print axioms Paper7MomentCounts.labelledExactCapacityQCard_six_kernel_statistic_pruned

end Paper7MomentCounts
