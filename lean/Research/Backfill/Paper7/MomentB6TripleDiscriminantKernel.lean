import Research.Backfill.Paper7.MomentB6SortedTripleDiscriminant

/-! UNCOMPILED exact-formula interfaces by /root/moment_b6_labelled_symbolic_2310.
The definitions below are symbolic candidates; no theorem here asserts that
the proposed kernels already equal the original fibres. Those obligations
are recorded separately. No kernel value is evaluated or assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

def labelledExactCapacityCard (n A B : ℕ) : ℕ :=
  Nat.card {z : Fin n → ℕ // (∑ i, z i) = A ∧ (∑ i, z i ^ 2) = B}
#print axioms Paper7MomentCounts.labelledExactCapacityCard

def labelledExactCapacityQCard (n A B Q : ℕ) : ℕ :=
  Nat.card {x : (Fin n → ℕ) × (Fin n → ℕ) //
    (∀ i, x.2 i ≤ x.1 i) ∧ (∑ i, x.1 i) = A ∧
      (∑ i, x.1 i ^ 2) = B ∧ (∑ i, x.2 i) = Q}
#print axioms Paper7MomentCounts.labelledExactCapacityQCard

def labelledPositiveTriangular (n : ℤ) : ℤ :=
  if n < 0 then 0 else ((n.toNat + 2).choose 2 : ℕ)
#print axioms Paper7MomentCounts.labelledPositiveTriangular

def labelledTripleQWeight (a b c Q : ℕ) : ℤ :=
  labelledPositiveTriangular Q -
    labelledPositiveTriangular ((Q : ℤ) - a - 1) -
    labelledPositiveTriangular ((Q : ℤ) - b - 1) -
    labelledPositiveTriangular ((Q : ℤ) - c - 1) +
    labelledPositiveTriangular ((Q : ℤ) - a - b - 2) +
    labelledPositiveTriangular ((Q : ℤ) - a - c - 2) +
    labelledPositiveTriangular ((Q : ℤ) - b - c - 2) -
    labelledPositiveTriangular ((Q : ℤ) - a - b - c - 3)
#print axioms Paper7MomentCounts.labelledTripleQWeight

def labelledSortedTripleMultiplicity (c a b : ℕ) : ℕ :=
  if c = a ∧ a = b then 1 else if c = a ∨ a = b then 3 else 6
#print axioms Paper7MomentCounts.labelledSortedTripleMultiplicity

def labelledTripleScalarRange (A B : ℕ) : Finset ℕ :=
  Finset.Icc ((A + 2) / 3) (min A (Nat.sqrt B))
#print axioms Paper7MomentCounts.labelledTripleScalarRange

def labelledTripleDiscriminantKernel (A B Q : ℕ) : ℤ :=
  ∑ c ∈ labelledTripleScalarRange A B,
    if B6SortedTripleDiscriminantAccept A B c then
      (labelledSortedTripleMultiplicity c
        (labelledTripleHigh A B c) (labelledTripleLow A B c) : ℤ) *
      labelledTripleQWeight c (labelledTripleHigh A B c) (labelledTripleLow A B c) Q
    else 0
#print axioms Paper7MomentCounts.labelledTripleDiscriminantKernel

def B6TripleStatisticGuard (A B : ℕ) : Prop :=
  A^2 ≤ 3*B ∧ B ≤ A^2 ∧ B%2 = A%2
#print axioms Paper7MomentCounts.B6TripleStatisticGuard

def labelledTripleQSplitRange (Z A Q : ℕ) : Finset ℕ :=
  Finset.Icc (Q - (Z-A)) (min Q A)
#print axioms Paper7MomentCounts.labelledTripleQSplitRange

def labelledTriplePairFactor (Z R A B : ℕ) : ℕ :=
  if 2*A = Z ∧ 2*B = R then 1 else 2
#print axioms Paper7MomentCounts.labelledTriplePairFactor

def labelledSixDiscriminantKernel (Z R Q : ℕ) : ℤ :=
  ∑ A ∈ Finset.range (Z / 2 + 1), ∑ B ∈ Finset.range (R + 1),
    if B6TripleStatisticGuard A B ∧
      B6TripleStatisticGuard (Z-A) (R-B) ∧ (2*A < Z ∨ 2*B ≤ R)
    then (labelledTriplePairFactor Z R A B : ℤ) *
      ∑ t ∈ labelledTripleQSplitRange Z A Q,
        labelledTripleDiscriminantKernel A B t *
          labelledTripleDiscriminantKernel (Z-A) (R-B) (Q-t)
    else 0
#print axioms Paper7MomentCounts.labelledSixDiscriminantKernel

def labelledPositiveFiveBinomial (n : ℤ) : ℤ :=
  if n < 0 then 0 else ((n.toNat + 5).choose 5 : ℕ)
#print axioms Paper7MomentCounts.labelledPositiveFiveBinomial

def labelledSixQWeight (z : Fin 6 → ℕ) (Q : ℕ) : ℤ :=
  ∑ I : Finset (Fin 6), (-1 : ℤ) ^ I.card *
    labelledPositiveFiveBinomial ((Q : ℤ) - (∑ i ∈ I, (z i : ℤ)) - I.card)
#print axioms Paper7MomentCounts.labelledSixQWeight

def labelledJoinedTripleCapacity (A B c D E f : ℕ) : Fin 6 → ℕ :=
  ![c, labelledTripleHigh A B c, labelledTripleLow A B c,
    f, labelledTripleHigh D E f, labelledTripleLow D E f]
#print axioms Paper7MomentCounts.labelledJoinedTripleCapacity

def labelledSixDiscriminantDirectKernel (Z R Q : ℕ) : ℤ :=
  ∑ A ∈ Finset.range (Z / 2 + 1), ∑ B ∈ Finset.range (R + 1),
    if B6TripleStatisticGuard A B ∧
      B6TripleStatisticGuard (Z-A) (R-B) ∧ (2*A < Z ∨ 2*B ≤ R)
    then (labelledTriplePairFactor Z R A B : ℤ) *
      ∑ c ∈ labelledTripleScalarRange A B,
        ∑ f ∈ labelledTripleScalarRange (Z-A) (R-B),
          if B6SortedTripleDiscriminantAccept A B c ∧
            B6SortedTripleDiscriminantAccept (Z-A) (R-B) f
          then (labelledSortedTripleMultiplicity c
              (labelledTripleHigh A B c) (labelledTripleLow A B c) : ℤ) *
            (labelledSortedTripleMultiplicity f
              (labelledTripleHigh (Z-A) (R-B) f) (labelledTripleLow (Z-A) (R-B) f) : ℤ) *
            labelledSixQWeight (labelledJoinedTripleCapacity A B c (Z-A) (R-B) f) Q
          else 0
    else 0
#print axioms Paper7MomentCounts.labelledSixDiscriminantDirectKernel

end Paper7MomentCounts
