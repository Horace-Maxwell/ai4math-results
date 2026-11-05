import Research.Backfill.Paper7.MomentB6Theta96Route

/-! Complete theta96 histogram coverage. The 54 rows below are indexed
representatives only: completeness is proved from the original mass,
second moment and six-position equations. Ordered permutations are restored
by the already proved histogram-fibre equivalence. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators

def b6Theta96Reference : Fin 54 → Fin 6 → Fin 8 :=
  ![![7,0,0,0,0,0], ![7,1,0,0,0,0], ![6,3,0,0,0,0], ![7,2,0,0,0,0],
    ![7,1,1,0,0,0], ![6,2,1,0,0,0], ![6,1,1,1,0,0], ![5,4,0,0,0,0],
    ![7,1,1,1,0,0], ![6,4,0,0,0,0], ![6,3,1,0,0,0], ![6,2,2,0,0,0],
    ![6,2,1,1,0,0], ![6,1,1,1,1,0], ![5,5,0,0,0,0], ![5,4,1,0,0,0],
    ![5,3,2,0,0,0], ![5,3,1,1,0,0], ![5,2,2,1,0,0], ![4,4,2,0,0,0],
    ![4,4,1,1,0,0], ![4,3,3,0,0,0],
    ![6,3,2,0,0,0], ![6,3,1,1,0,0], ![6,2,2,1,0,0], ![6,2,1,1,1,0],
    ![6,1,1,1,1,1], ![5,5,1,0,0,0], ![5,4,2,0,0,0], ![5,4,1,1,0,0],
    ![5,3,3,0,0,0], ![5,3,2,1,0,0], ![5,3,1,1,1,0], ![5,2,2,2,0,0],
    ![5,2,2,1,1,0], ![5,2,1,1,1,1], ![4,4,3,0,0,0], ![4,4,2,1,0,0],
    ![4,4,1,1,1,0], ![4,3,3,1,0,0], ![4,3,2,2,0,0], ![4,3,2,1,1,0],
    ![4,3,1,1,1,1], ![4,2,2,2,1,0], ![3,3,3,2,0,0], ![3,3,3,1,1,0],
    ![6,3,1,1,1,0], ![6,2,2,2,0,0], ![6,2,2,1,1,0], ![5,4,2,1,0,0],
    ![4,4,4,0,0,0], ![5,4,1,1,1,1], ![5,3,3,1,1,0], ![4,4,3,2,0,0]]
#print axioms Paper7MomentCounts.b6Theta96Reference

def b6Theta96Profile : Fin 54 → Fin 8 → ℕ :=
  ![![5,0,0,0,0,0,0,1], ![4,1,0,0,0,0,0,1], ![4,0,0,1,0,0,1,0],
    ![4,0,1,0,0,0,0,1], ![3,2,0,0,0,0,0,1], ![3,1,1,0,0,0,1,0],
    ![2,3,0,0,0,0,1,0], ![4,0,0,0,1,1,0,0],
    ![2,3,0,0,0,0,0,1], ![4,0,0,0,1,0,1,0], ![3,1,0,1,0,0,1,0],
    ![3,0,2,0,0,0,1,0], ![2,2,1,0,0,0,1,0], ![1,4,0,0,0,0,1,0],
    ![4,0,0,0,0,2,0,0], ![3,1,0,0,1,1,0,0], ![3,0,1,1,0,1,0,0],
    ![2,2,0,1,0,1,0,0], ![2,1,2,0,0,1,0,0], ![3,0,1,0,2,0,0,0],
    ![2,2,0,0,2,0,0,0], ![3,0,0,2,1,0,0,0],
    ![3,0,1,1,0,0,1,0], ![2,2,0,1,0,0,1,0], ![2,1,2,0,0,0,1,0],
    ![1,3,1,0,0,0,1,0], ![0,5,0,0,0,0,1,0], ![3,1,0,0,0,2,0,0],
    ![3,0,1,0,1,1,0,0], ![2,2,0,0,1,1,0,0], ![3,0,0,2,0,1,0,0],
    ![2,1,1,1,0,1,0,0], ![1,3,0,1,0,1,0,0], ![2,0,3,0,0,1,0,0],
    ![1,2,2,0,0,1,0,0], ![0,4,1,0,0,1,0,0], ![3,0,0,1,2,0,0,0],
    ![2,1,1,0,2,0,0,0], ![1,3,0,0,2,0,0,0], ![2,1,0,2,1,0,0,0],
    ![2,0,2,1,1,0,0,0], ![1,2,1,1,1,0,0,0], ![0,4,0,1,1,0,0,0],
    ![1,1,3,0,1,0,0,0], ![2,0,1,3,0,0,0,0], ![1,2,0,3,0,0,0,0],
    ![1,3,0,1,0,0,1,0], ![2,0,3,0,0,0,1,0], ![1,2,2,0,0,0,1,0],
    ![2,1,1,0,1,1,0,0], ![3,0,0,0,3,0,0,0], ![0,4,0,0,1,1,0,0],
    ![1,2,0,2,0,1,0,0], ![2,0,1,1,2,0,0,0]]
#print axioms Paper7MomentCounts.b6Theta96Profile

def b6Theta96Q : Fin 54 → ℕ :=
  ![7,5,6,2,3,8,9,8, 1,1,4,5,6,7,2,6,8,9,10,9,10,10,
    1,2,3,4,5,0,3,4,4,6,7,7,8,9,5,7,8,8,9,10,11,11,10,11,
    0,0,1,1,0,0,0,0]
#print axioms Paper7MomentCounts.b6Theta96Q

def b6Theta96Nat (j : Fin 54) (i : Fin 6) : ℕ := (b6Theta96Reference j i).val
#print axioms Paper7MomentCounts.b6Theta96Nat

theorem b6Theta96Reference_histogram : ∀ j : Fin 54,
    finiteValueHistogram (b6Theta96Reference j) = b6Theta96Profile j := by decide +kernel
#print axioms Paper7MomentCounts.b6Theta96Reference_histogram

theorem b6Theta96Reference_data : ∀ j : Fin 54,
    B6Theta96Data (b6Theta96Nat j) (b6Theta96Q j) := by
  unfold B6Theta96Data
  decide +kernel
#print axioms Paper7MomentCounts.b6Theta96Reference_data

theorem b6Theta96Profile_injective : Function.Injective b6Theta96Profile := by decide +kernel
#print axioms Paper7MomentCounts.b6Theta96Profile_injective

def b6Theta96TenIndex (j : Fin 14) : Fin 54 := ⟨j.val + 8,by omega⟩
#print axioms Paper7MomentCounts.b6Theta96TenIndex

theorem b6Theta96_ten_profile : ∀ j : Fin 14,
    b6Theta96Profile (b6Theta96TenIndex j) = b6TenProfile j ∧
      b6Theta96Q (b6Theta96TenIndex j) = b6TenProfileQ j := by decide +kernel
#print axioms Paper7MomentCounts.b6Theta96_ten_profile

local macro "b6_theta96_profile " j:term : tactic =>
  `(tactic| (refine ⟨$j,?_,?_⟩ <;> first
    | (funext v; fin_cases v <;> norm_num [b6Theta96Profile] <;> omega)
    | (norm_num [b6Theta96Q]; omega)))

def B6Theta96HistogramReducedData (a : Fin 8 → ℕ) (Z Q : ℕ) : Prop :=
  (a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6) ∧
  (a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = Z) ∧
  (a 2+3*a 3+6*a 4+10*a 5+15*a 6+21*a 7+Q+2*Z = 42) ∧
  Q ≤ Z ∧ 11 ≤ Z+Q ∧ (2 ≤ Q → Z ≤ 11) ∧ (Q ≤ 1 → Z+Q ≤ 13)
#print axioms Paper7MomentCounts.B6Theta96HistogramReducedData

theorem b6Theta96Histogram_halfMoment (a : Fin 8 → ℕ) (Z Q : ℕ)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = Z)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*Z+2*Q = 84) :
    a 2+3*a 3+6*a 4+10*a 5+15*a 6+21*a 7+Q+2*Z = 42 := by
  omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_halfMoment

theorem b6Theta96Histogram_mass_cases (Z : ℕ) (hlo : 7 ≤ Z) (hhi : Z ≤ 13) :
    Z = 7 ∨ Z = 8 ∨ Z = 9 ∨ Z = 10 ∨ Z = 11 ∨ Z = 12 ∨ Z = 13 := by
  omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_mass_cases

theorem b6Theta96Histogram_case0 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 7 Q) (hcase : a 7 = 1) :
    a = b6Theta96Profile 0 ∧ Q = b6Theta96Q 0 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  have h7 := hcase
  constructor
  · funext v
    fin_cases v
    · change a 0 = 5
      omega
    · change a 1 = 0
      omega
    · change a 2 = 0
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 1
      omega
  · change Q = 7
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case0

theorem b6Theta96Histogram_case1 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 8 Q) (hcase : a 7 = 1) :
    a = b6Theta96Profile 1 ∧ Q = b6Theta96Q 1 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  have h7 := hcase
  have hz2 : a 2 = 0 := by omega
  have hz3 : a 3 = 0 := by omega
  have hz4 : a 4 = 0 := by omega
  have hz5 : a 5 = 0 := by omega
  have hz6 : a 6 = 0 := by omega
  constructor
  · funext v
    fin_cases v
    · change a 0 = 4
      omega
    · change a 1 = 1
      omega
    · change a 2 = 0
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 1
      omega
  · change Q = 5
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case1

theorem b6Theta96Histogram_case2 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 9 Q) (hcase : a 7 = 0 ∧ a 6 = 1 ∧ a 5 = 0 ∧ a 4 = 0 ∧ a 3 = 1) :
    a = b6Theta96Profile 2 ∧ Q = b6Theta96Q 2 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 4
      omega
    · change a 1 = 0
      omega
    · change a 2 = 0
      omega
    · change a 3 = 1
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 1
      omega
    · change a 7 = 0
      omega
  · change Q = 6
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case2

theorem b6Theta96Histogram_case3 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 9 Q) (hcase : a 7 = 1 ∧ a 2 = 1) :
    a = b6Theta96Profile 3 ∧ Q = b6Theta96Q 3 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 4
      omega
    · change a 1 = 0
      omega
    · change a 2 = 1
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 1
      omega
  · change Q = 2
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case3

theorem b6Theta96Histogram_case4 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 9 Q) (hcase : a 7 = 1 ∧ a 2 = 0) :
    a = b6Theta96Profile 4 ∧ Q = b6Theta96Q 4 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h2⟩
  have hz3 : a 3 = 0 := by omega
  have hz4 : a 4 = 0 := by omega
  have hz5 : a 5 = 0 := by omega
  have hz6 : a 6 = 0 := by omega
  constructor
  · funext v
    fin_cases v
    · change a 0 = 3
      omega
    · change a 1 = 2
      omega
    · change a 2 = 0
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 1
      omega
  · change Q = 3
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case4

theorem b6Theta96Histogram_case5 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 9 Q) (hcase : a 7 = 0 ∧ a 6 = 1 ∧ a 5 = 0 ∧ a 4 = 0 ∧ a 3 = 0 ∧ a 2 = 1) :
    a = b6Theta96Profile 5 ∧ Q = b6Theta96Q 5 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 3
      omega
    · change a 1 = 1
      omega
    · change a 2 = 1
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 1
      omega
    · change a 7 = 0
      omega
  · change Q = 8
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case5

theorem b6Theta96Histogram_case6 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 9 Q) (hcase : a 7 = 0 ∧ a 6 = 1 ∧ a 5 = 0 ∧ a 4 = 0 ∧ a 3 = 0 ∧ a 2 = 0) :
    a = b6Theta96Profile 6 ∧ Q = b6Theta96Q 6 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 3
      omega
    · change a 2 = 0
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 1
      omega
    · change a 7 = 0
      omega
  · change Q = 9
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case6

theorem b6Theta96Histogram_case7 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 9 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 1) :
    a = b6Theta96Profile 7 ∧ Q = b6Theta96Q 7 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 4
      omega
    · change a 1 = 0
      omega
    · change a 2 = 0
      omega
    · change a 3 = 0
      omega
    · change a 4 = 1
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 8
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case7

theorem b6Theta96Histogram_case22 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 1 ∧ a 5 = 0 ∧ a 4 = 0 ∧ a 3 = 1 ∧ a 2 = 1) :
    a = b6Theta96Profile 22 ∧ Q = b6Theta96Q 22 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 3
      omega
    · change a 1 = 0
      omega
    · change a 2 = 1
      omega
    · change a 3 = 1
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 1
      omega
    · change a 7 = 0
      omega
  · change Q = 1
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case22

theorem b6Theta96Histogram_case23 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 1 ∧ a 5 = 0 ∧ a 4 = 0 ∧ a 3 = 1 ∧ a 2 = 0) :
    a = b6Theta96Profile 23 ∧ Q = b6Theta96Q 23 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 2
      omega
    · change a 2 = 0
      omega
    · change a 3 = 1
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 1
      omega
    · change a 7 = 0
      omega
  · change Q = 2
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case23

theorem b6Theta96Histogram_case24 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 1 ∧ a 5 = 0 ∧ a 4 = 0 ∧ a 3 = 0 ∧ a 2 = 2) :
    a = b6Theta96Profile 24 ∧ Q = b6Theta96Q 24 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 1
      omega
    · change a 2 = 2
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 1
      omega
    · change a 7 = 0
      omega
  · change Q = 3
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case24

theorem b6Theta96Histogram_case25 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 1 ∧ a 5 = 0 ∧ a 4 = 0 ∧ a 3 = 0 ∧ a 2 = 1) :
    a = b6Theta96Profile 25 ∧ Q = b6Theta96Q 25 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 1
      omega
    · change a 1 = 3
      omega
    · change a 2 = 1
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 1
      omega
    · change a 7 = 0
      omega
  · change Q = 4
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case25

theorem b6Theta96Histogram_case26 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 1 ∧ a 5 = 0 ∧ a 4 = 0 ∧ a 3 = 0 ∧ a 2 = 0) :
    a = b6Theta96Profile 26 ∧ Q = b6Theta96Q 26 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 0
      omega
    · change a 1 = 5
      omega
    · change a 2 = 0
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 1
      omega
    · change a 7 = 0
      omega
  · change Q = 5
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case26

theorem b6Theta96Histogram_case27 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 2) :
    a = b6Theta96Profile 27 ∧ Q = b6Theta96Q 27 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 3
      omega
    · change a 1 = 1
      omega
    · change a 2 = 0
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 2
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 0
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case27

theorem b6Theta96Histogram_case28 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 1 ∧ a 2 = 1) :
    a = b6Theta96Profile 28 ∧ Q = b6Theta96Q 28 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 3
      omega
    · change a 1 = 0
      omega
    · change a 2 = 1
      omega
    · change a 3 = 0
      omega
    · change a 4 = 1
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 3
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case28

theorem b6Theta96Histogram_case29 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 1 ∧ a 2 = 0) :
    a = b6Theta96Profile 29 ∧ Q = b6Theta96Q 29 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 2
      omega
    · change a 2 = 0
      omega
    · change a 3 = 0
      omega
    · change a 4 = 1
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 4
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case29

theorem b6Theta96Histogram_case30 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 0 ∧ a 3 = 2) :
    a = b6Theta96Profile 30 ∧ Q = b6Theta96Q 30 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 3
      omega
    · change a 1 = 0
      omega
    · change a 2 = 0
      omega
    · change a 3 = 2
      omega
    · change a 4 = 0
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 4
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case30

theorem b6Theta96Histogram_case31 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 0 ∧ a 3 = 1 ∧ a 2 = 1) :
    a = b6Theta96Profile 31 ∧ Q = b6Theta96Q 31 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 1
      omega
    · change a 2 = 1
      omega
    · change a 3 = 1
      omega
    · change a 4 = 0
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 6
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case31

theorem b6Theta96Histogram_case32 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 0 ∧ a 3 = 1 ∧ a 2 = 0) :
    a = b6Theta96Profile 32 ∧ Q = b6Theta96Q 32 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 1
      omega
    · change a 1 = 3
      omega
    · change a 2 = 0
      omega
    · change a 3 = 1
      omega
    · change a 4 = 0
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 7
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case32

theorem b6Theta96Histogram_case33 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 0 ∧ a 3 = 0 ∧ a 2 = 3) :
    a = b6Theta96Profile 33 ∧ Q = b6Theta96Q 33 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 0
      omega
    · change a 2 = 3
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 7
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case33

theorem b6Theta96Histogram_case34 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 0 ∧ a 3 = 0 ∧ a 2 = 2) :
    a = b6Theta96Profile 34 ∧ Q = b6Theta96Q 34 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 1
      omega
    · change a 1 = 2
      omega
    · change a 2 = 2
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 8
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case34

theorem b6Theta96Histogram_case35 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 0 ∧ a 3 = 0 ∧ a 2 = 1) :
    a = b6Theta96Profile 35 ∧ Q = b6Theta96Q 35 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 0
      omega
    · change a 1 = 4
      omega
    · change a 2 = 1
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 9
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case35

theorem b6Theta96Histogram_case36 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0 ∧ a 4 = 2 ∧ a 3 = 1) :
    a = b6Theta96Profile 36 ∧ Q = b6Theta96Q 36 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 3
      omega
    · change a 1 = 0
      omega
    · change a 2 = 0
      omega
    · change a 3 = 1
      omega
    · change a 4 = 2
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 5
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case36

theorem b6Theta96Histogram_case37 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0 ∧ a 4 = 2 ∧ a 3 = 0 ∧ a 2 = 1) :
    a = b6Theta96Profile 37 ∧ Q = b6Theta96Q 37 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 1
      omega
    · change a 2 = 1
      omega
    · change a 3 = 0
      omega
    · change a 4 = 2
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 7
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case37

theorem b6Theta96Histogram_case38 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0 ∧ a 4 = 2 ∧ a 3 = 0 ∧ a 2 = 0) :
    a = b6Theta96Profile 38 ∧ Q = b6Theta96Q 38 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 1
      omega
    · change a 1 = 3
      omega
    · change a 2 = 0
      omega
    · change a 3 = 0
      omega
    · change a 4 = 2
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 8
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case38

theorem b6Theta96Histogram_case39 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0 ∧ a 4 = 1 ∧ a 3 = 2) :
    a = b6Theta96Profile 39 ∧ Q = b6Theta96Q 39 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 1
      omega
    · change a 2 = 0
      omega
    · change a 3 = 2
      omega
    · change a 4 = 1
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 8
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case39

theorem b6Theta96Histogram_case40 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0 ∧ a 4 = 1 ∧ a 3 = 1 ∧ a 2 = 2) :
    a = b6Theta96Profile 40 ∧ Q = b6Theta96Q 40 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 0
      omega
    · change a 2 = 2
      omega
    · change a 3 = 1
      omega
    · change a 4 = 1
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 9
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case40

theorem b6Theta96Histogram_case41 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0 ∧ a 4 = 1 ∧ a 3 = 1 ∧ a 2 = 1) :
    a = b6Theta96Profile 41 ∧ Q = b6Theta96Q 41 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 1
      omega
    · change a 1 = 2
      omega
    · change a 2 = 1
      omega
    · change a 3 = 1
      omega
    · change a 4 = 1
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 10
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case41

theorem b6Theta96Histogram_case42 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0 ∧ a 4 = 1 ∧ a 3 = 1 ∧ a 2 = 0) :
    a = b6Theta96Profile 42 ∧ Q = b6Theta96Q 42 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 0
      omega
    · change a 1 = 4
      omega
    · change a 2 = 0
      omega
    · change a 3 = 1
      omega
    · change a 4 = 1
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 11
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case42

theorem b6Theta96Histogram_case43 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0 ∧ a 4 = 1 ∧ a 3 = 0 ∧ a 2 = 3) :
    a = b6Theta96Profile 43 ∧ Q = b6Theta96Q 43 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 1
      omega
    · change a 1 = 1
      omega
    · change a 2 = 3
      omega
    · change a 3 = 0
      omega
    · change a 4 = 1
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 11
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case43

theorem b6Theta96Histogram_case44 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0 ∧ a 4 = 0 ∧ a 3 = 3 ∧ a 2 = 1) :
    a = b6Theta96Profile 44 ∧ Q = b6Theta96Q 44 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 0
      omega
    · change a 2 = 1
      omega
    · change a 3 = 3
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 10
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case44

theorem b6Theta96Histogram_case45 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 11 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0 ∧ a 4 = 0 ∧ a 3 = 3 ∧ a 2 = 0) :
    a = b6Theta96Profile 45 ∧ Q = b6Theta96Q 45 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,h3,h2⟩
  constructor
  · funext v
    fin_cases v
    · change a 0 = 1
      omega
    · change a 1 = 2
      omega
    · change a 2 = 0
      omega
    · change a 3 = 3
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 11
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case45

theorem b6Theta96Histogram_case46 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 12 Q) (hcase : a 7 = 0 ∧ a 6 = 1 ∧ a 5 = 0 ∧ a 4 = 0 ∧ Q = 0 ∧ a 3 = 1) :
    a = b6Theta96Profile 46 ∧ Q = b6Theta96Q 46 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,hQ,h3⟩
  have hQ1 : Q ≤ 1 := by
    by_contra hn
    have hbad := hlarge (by omega)
    omega
  constructor
  · funext v
    fin_cases v
    · change a 0 = 1
      omega
    · change a 1 = 3
      omega
    · change a 2 = 0
      omega
    · change a 3 = 1
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 1
      omega
    · change a 7 = 0
      omega
  · change Q = 0
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case46

theorem b6Theta96Histogram_case47 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 12 Q) (hcase : a 7 = 0 ∧ a 6 = 1 ∧ a 5 = 0 ∧ a 4 = 0 ∧ Q = 0 ∧ a 3 = 0) :
    a = b6Theta96Profile 47 ∧ Q = b6Theta96Q 47 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,hQ,h3⟩
  have hQ1 : Q ≤ 1 := by
    by_contra hn
    have hbad := hlarge (by omega)
    omega
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 0
      omega
    · change a 2 = 3
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 1
      omega
    · change a 7 = 0
      omega
  · change Q = 0
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case47

theorem b6Theta96Histogram_case48 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 12 Q) (hcase : a 7 = 0 ∧ a 6 = 1 ∧ a 5 = 0 ∧ a 4 = 0 ∧ Q = 1) :
    a = b6Theta96Profile 48 ∧ Q = b6Theta96Q 48 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,hQ⟩
  have hQ1 : Q ≤ 1 := by
    by_contra hn
    have hbad := hlarge (by omega)
    omega
  constructor
  · funext v
    fin_cases v
    · change a 0 = 1
      omega
    · change a 1 = 2
      omega
    · change a 2 = 2
      omega
    · change a 3 = 0
      omega
    · change a 4 = 0
      omega
    · change a 5 = 0
      omega
    · change a 6 = 1
      omega
    · change a 7 = 0
      omega
  · change Q = 1
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case48

theorem b6Theta96Histogram_case49 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 12 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 1 ∧ Q = 1) :
    a = b6Theta96Profile 49 ∧ Q = b6Theta96Q 49 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4,hQ⟩
  have hQ1 : Q ≤ 1 := by
    by_contra hn
    have hbad := hlarge (by omega)
    omega
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 1
      omega
    · change a 2 = 1
      omega
    · change a 3 = 0
      omega
    · change a 4 = 1
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 1
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case49

theorem b6Theta96Histogram_case50 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 12 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0) :
    a = b6Theta96Profile 50 ∧ Q = b6Theta96Q 50 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5⟩
  have hQ1 : Q ≤ 1 := by
    by_contra hn
    have hbad := hlarge (by omega)
    omega
  constructor
  · funext v
    fin_cases v
    · change a 0 = 3
      omega
    · change a 1 = 0
      omega
    · change a 2 = 0
      omega
    · change a 3 = 0
      omega
    · change a 4 = 3
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 0
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case50

theorem b6Theta96Histogram_case51 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 13 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 1) :
    a = b6Theta96Profile 51 ∧ Q = b6Theta96Q 51 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4⟩
  have hQ1 : Q ≤ 1 := by
    by_contra hn
    have hbad := hlarge (by omega)
    omega
  have hq : Q = 0 := by
    have hbound := hsmall hQ1
    omega
  constructor
  · funext v
    fin_cases v
    · change a 0 = 0
      omega
    · change a 1 = 4
      omega
    · change a 2 = 0
      omega
    · change a 3 = 0
      omega
    · change a 4 = 1
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 0
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case51

theorem b6Theta96Histogram_case52 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 13 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 1 ∧ a 4 = 0) :
    a = b6Theta96Profile 52 ∧ Q = b6Theta96Q 52 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4⟩
  have hQ1 : Q ≤ 1 := by
    by_contra hn
    have hbad := hlarge (by omega)
    omega
  have hq : Q = 0 := by
    have hbound := hsmall hQ1
    omega
  constructor
  · funext v
    fin_cases v
    · change a 0 = 1
      omega
    · change a 1 = 2
      omega
    · change a 2 = 0
      omega
    · change a 3 = 2
      omega
    · change a 4 = 0
      omega
    · change a 5 = 1
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 0
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case52

theorem b6Theta96Histogram_case53 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6Theta96HistogramReducedData a 13 Q) (hcase : a 7 = 0 ∧ a 6 = 0 ∧ a 5 = 0 ∧ a 4 = 2) :
    a = b6Theta96Profile 53 ∧ Q = b6Theta96Q 53 := by
  rcases h with ⟨hc,hs,hm,hQ,hload,hlarge,hsmall⟩
  rcases hcase with ⟨h7,h6,h5,h4⟩
  have hQ1 : Q ≤ 1 := by
    by_contra hn
    have hbad := hlarge (by omega)
    omega
  have hq : Q = 0 := by
    have hbound := hsmall hQ1
    omega
  constructor
  · funext v
    fin_cases v
    · change a 0 = 2
      omega
    · change a 1 = 0
      omega
    · change a 2 = 1
      omega
    · change a 3 = 1
      omega
    · change a 4 = 2
      omega
    · change a 5 = 0
      omega
    · change a 6 = 0
      omega
    · change a 7 = 0
      omega
  · change Q = 0
    omega
#print axioms Paper7MomentCounts.b6Theta96Histogram_case53

theorem b6Theta96Histogram_z11_a6_one (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 11)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*11+2*Q = 84)
    (hQ : Q ≤ 11) (hload : 11 ≤ 11+Q)
    (hlarge : 2 ≤ Q → 11 ≤ 11) (hsmall : Q ≤ 1 → 11+Q ≤ 13)
    (hz7 : a 7 = 0) (h6 : a 6 = 1) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 11 Q hs hm
  have hd : B6Theta96HistogramReducedData a 11 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  have hz5 : a 5 = 0 := by omega
  have hz4 : a 4 = 0 := by omega
  by_cases h3 : a 3 = 1
  · by_cases h2 : a 2 = 1
    · exact ⟨22,b6Theta96Histogram_case22 a Q hd ⟨hz7,h6,hz5,hz4,h3,h2⟩⟩
    · have hz2 : a 2 = 0 := by omega
      exact ⟨23,b6Theta96Histogram_case23 a Q hd ⟨hz7,h6,hz5,hz4,h3,hz2⟩⟩
  · have hz3 : a 3 = 0 := by omega
    by_cases h22 : a 2 = 2
    · exact ⟨24,b6Theta96Histogram_case24 a Q hd ⟨hz7,h6,hz5,hz4,hz3,h22⟩⟩
    · by_cases h21 : a 2 = 1
      · exact ⟨25,b6Theta96Histogram_case25 a Q hd ⟨hz7,h6,hz5,hz4,hz3,h21⟩⟩
      · have hz2 : a 2 = 0 := by omega
        exact ⟨26,b6Theta96Histogram_case26 a Q hd ⟨hz7,h6,hz5,hz4,hz3,hz2⟩⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z11_a6_one

theorem b6Theta96Histogram_z11_a5_one_a4_one (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 11)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*11+2*Q = 84)
    (hQ : Q ≤ 11) (hload : 11 ≤ 11+Q)
    (hlarge : 2 ≤ Q → 11 ≤ 11) (hsmall : Q ≤ 1 → 11+Q ≤ 13)
    (hz7 : a 7 = 0) (hz6 : a 6 = 0) (h51 : a 5 = 1) (h4 : a 4 = 1) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 11 Q hs hm
  have hd : B6Theta96HistogramReducedData a 11 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  by_cases h2 : a 2 = 1
  · exact ⟨28,b6Theta96Histogram_case28 a Q hd ⟨hz7,hz6,h51,h4,h2⟩⟩
  · have hz2 : a 2 = 0 := by omega
    exact ⟨29,b6Theta96Histogram_case29 a Q hd ⟨hz7,hz6,h51,h4,hz2⟩⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z11_a5_one_a4_one

theorem b6Theta96Histogram_z11_a5_one_a4_rest (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 11)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*11+2*Q = 84)
    (hQ : Q ≤ 11) (hload : 11 ≤ 11+Q)
    (hlarge : 2 ≤ Q → 11 ≤ 11) (hsmall : Q ≤ 1 → 11+Q ≤ 13)
    (hz7 : a 7 = 0) (hz6 : a 6 = 0) (h51 : a 5 = 1) (h4 : a 4 ≠ 1) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 11 Q hs hm
  have hd : B6Theta96HistogramReducedData a 11 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  have hz4 : a 4 = 0 := by omega
  by_cases h32 : a 3 = 2
  · exact ⟨30,b6Theta96Histogram_case30 a Q hd ⟨hz7,hz6,h51,hz4,h32⟩⟩
  · by_cases h31 : a 3 = 1
    · by_cases h2 : a 2 = 1
      · exact ⟨31,b6Theta96Histogram_case31 a Q hd ⟨hz7,hz6,h51,hz4,h31,h2⟩⟩
      · have hz2 : a 2 = 0 := by omega
        exact ⟨32,b6Theta96Histogram_case32 a Q hd ⟨hz7,hz6,h51,hz4,h31,hz2⟩⟩
    · have hz3 : a 3 = 0 := by omega
      by_cases h23 : a 2 = 3
      · exact ⟨33,b6Theta96Histogram_case33 a Q hd ⟨hz7,hz6,h51,hz4,hz3,h23⟩⟩
      · by_cases h22 : a 2 = 2
        · exact ⟨34,b6Theta96Histogram_case34 a Q hd ⟨hz7,hz6,h51,hz4,hz3,h22⟩⟩
        · have h21 : a 2 = 1 := by omega
          exact ⟨35,b6Theta96Histogram_case35 a Q hd ⟨hz7,hz6,h51,hz4,hz3,h21⟩⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z11_a5_one_a4_rest

theorem b6Theta96Histogram_z11_a4_two (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 11)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*11+2*Q = 84)
    (hQ : Q ≤ 11) (hload : 11 ≤ 11+Q)
    (hlarge : 2 ≤ Q → 11 ≤ 11) (hsmall : Q ≤ 1 → 11+Q ≤ 13)
    (hz7 : a 7 = 0) (hz6 : a 6 = 0) (hz5 : a 5 = 0) (h42 : a 4 = 2) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 11 Q hs hm
  have hd : B6Theta96HistogramReducedData a 11 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  by_cases h3 : a 3 = 1
  · exact ⟨36,b6Theta96Histogram_case36 a Q hd ⟨hz7,hz6,hz5,h42,h3⟩⟩
  · have hz3 : a 3 = 0 := by omega
    by_cases h2 : a 2 = 1
    · exact ⟨37,b6Theta96Histogram_case37 a Q hd ⟨hz7,hz6,hz5,h42,hz3,h2⟩⟩
    · have hz2 : a 2 = 0 := by omega
      exact ⟨38,b6Theta96Histogram_case38 a Q hd ⟨hz7,hz6,hz5,h42,hz3,hz2⟩⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z11_a4_two

theorem b6Theta96Histogram_z11_a4_one (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 11)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*11+2*Q = 84)
    (hQ : Q ≤ 11) (hload : 11 ≤ 11+Q)
    (hlarge : 2 ≤ Q → 11 ≤ 11) (hsmall : Q ≤ 1 → 11+Q ≤ 13)
    (hz7 : a 7 = 0) (hz6 : a 6 = 0) (hz5 : a 5 = 0) (h41 : a 4 = 1) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 11 Q hs hm
  have hd : B6Theta96HistogramReducedData a 11 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  by_cases h32 : a 3 = 2
  · exact ⟨39,b6Theta96Histogram_case39 a Q hd ⟨hz7,hz6,hz5,h41,h32⟩⟩
  · by_cases h31 : a 3 = 1
    · by_cases h22 : a 2 = 2
      · exact ⟨40,b6Theta96Histogram_case40 a Q hd ⟨hz7,hz6,hz5,h41,h31,h22⟩⟩
      · by_cases h21 : a 2 = 1
        · exact ⟨41,b6Theta96Histogram_case41 a Q hd ⟨hz7,hz6,hz5,h41,h31,h21⟩⟩
        · have hz2 : a 2 = 0 := by omega
          exact ⟨42,b6Theta96Histogram_case42 a Q hd ⟨hz7,hz6,hz5,h41,h31,hz2⟩⟩
    · have hz3 : a 3 = 0 := by omega
      have h23 : a 2 = 3 := by omega
      exact ⟨43,b6Theta96Histogram_case43 a Q hd ⟨hz7,hz6,hz5,h41,hz3,h23⟩⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z11_a4_one

theorem b6Theta96Histogram_z11_a4_rest (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 11)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*11+2*Q = 84)
    (hQ : Q ≤ 11) (hload : 11 ≤ 11+Q)
    (hlarge : 2 ≤ Q → 11 ≤ 11) (hsmall : Q ≤ 1 → 11+Q ≤ 13)
    (hz7 : a 7 = 0) (hz6 : a 6 = 0) (hz5 : a 5 = 0) (h42 : a 4 ≠ 2) (h41 : a 4 ≠ 1) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 11 Q hs hm
  have hd : B6Theta96HistogramReducedData a 11 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  have hz4 : a 4 = 0 := by omega
  have h33 : a 3 = 3 := by omega
  by_cases h2 : a 2 = 1
  · exact ⟨44,b6Theta96Histogram_case44 a Q hd ⟨hz7,hz6,hz5,hz4,h33,h2⟩⟩
  · have hz2 : a 2 = 0 := by omega
    exact ⟨45,b6Theta96Histogram_case45 a Q hd ⟨hz7,hz6,hz5,hz4,h33,hz2⟩⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z11_a4_rest

theorem b6Theta96Histogram_z7_cover (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 7)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*7+2*Q = 84)
    (hQ : Q ≤ 7) (hload : 11 ≤ 7+Q)
    (hlarge : 2 ≤ Q → 7 ≤ 11) (hsmall : Q ≤ 1 → 7+Q ≤ 13) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 7 Q hs hm
  have hd : B6Theta96HistogramReducedData a 7 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  have h7 : a 7 = 1 := by
    by_contra hn
    have hz7 : a 7 = 0 := by omega
    omega
  exact ⟨0,b6Theta96Histogram_case0 a Q hd h7⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z7_cover

theorem b6Theta96Histogram_z8_cover (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 8)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*8+2*Q = 84)
    (hQ : Q ≤ 8) (hload : 11 ≤ 8+Q)
    (hlarge : 2 ≤ Q → 8 ≤ 11) (hsmall : Q ≤ 1 → 8+Q ≤ 13) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 8 Q hs hm
  have hd : B6Theta96HistogramReducedData a 8 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  have h7 : a 7 = 1 := by
    by_contra hn
    have hz7 : a 7 = 0 := by omega
    by_cases h6 : a 6 = 1
    · have hz3 : a 3 = 0 := by omega
      have hz4 : a 4 = 0 := by omega
      have hz5 : a 5 = 0 := by omega
      omega
    · have hz6 : a 6 = 0 := by omega
      omega
  exact ⟨1,b6Theta96Histogram_case1 a Q hd h7⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z8_cover

theorem b6Theta96Histogram_z9_cover (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 9)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*9+2*Q = 84)
    (hQ : Q ≤ 9) (hload : 11 ≤ 9+Q)
    (hlarge : 2 ≤ Q → 9 ≤ 11) (hsmall : Q ≤ 1 → 9+Q ≤ 13) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 9 Q hs hm
  have hd : B6Theta96HistogramReducedData a 9 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  by_cases h7 : a 7 = 1
  · by_cases h2 : a 2 = 1
    · exact ⟨3,b6Theta96Histogram_case3 a Q hd ⟨h7,h2⟩⟩
    · have hz2 : a 2 = 0 := by omega
      exact ⟨4,b6Theta96Histogram_case4 a Q hd ⟨h7,hz2⟩⟩
  · have hz7 : a 7 = 0 := by omega
    by_cases h6 : a 6 = 1
    · have hz4 : a 4 = 0 := by omega
      have hz5 : a 5 = 0 := by omega
      by_cases h3 : a 3 = 1
      · exact ⟨2,b6Theta96Histogram_case2 a Q hd ⟨hz7,h6,hz5,hz4,h3⟩⟩
      · have hz3 : a 3 = 0 := by omega
        by_cases h2 : a 2 = 1
        · exact ⟨5,b6Theta96Histogram_case5 a Q hd ⟨hz7,h6,hz5,hz4,hz3,h2⟩⟩
        · have hz2 : a 2 = 0 := by omega
          exact ⟨6,b6Theta96Histogram_case6 a Q hd ⟨hz7,h6,hz5,hz4,hz3,hz2⟩⟩
    · have hz6 : a 6 = 0 := by omega
      have h5 : a 5 = 1 := by
        by_contra hn
        have hz5 : a 5 = 0 := by omega
        omega
      have h4 : a 4 = 1 := by
        by_contra hn
        have hz4 : a 4 = 0 := by omega
        omega
      exact ⟨7,b6Theta96Histogram_case7 a Q hd ⟨hz7,hz6,h5,h4⟩⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z9_cover

theorem b6Theta96Histogram_z10_cover (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 10)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*10+2*Q = 84)
    (hQ : Q ≤ 10) (hload : 11 ≤ 10+Q)
    (hlarge : 2 ≤ Q → 10 ≤ 11) (hsmall : Q ≤ 1 → 10+Q ≤ 13) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 10 Q hs hm
  have hd : B6Theta96HistogramReducedData a 10 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  rcases hd with ⟨hc',hs',hh',hQ',hload',hlarge',hsmall'⟩
  obtain ⟨j,hp,hq⟩ := b6TenHistogram_linear_cover a Q hc' hs' (by omega) (by omega) hQ'
  have he := b6Theta96_ten_profile j
  exact ⟨b6Theta96TenIndex j,hp.trans he.1.symm,hq.trans he.2.symm⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z10_cover

theorem b6Theta96Histogram_z11_cover (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 11)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*11+2*Q = 84)
    (hQ : Q ≤ 11) (hload : 11 ≤ 11+Q)
    (hlarge : 2 ≤ Q → 11 ≤ 11) (hsmall : Q ≤ 1 → 11+Q ≤ 13) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 11 Q hs hm
  have hd : B6Theta96HistogramReducedData a 11 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  have hz7 : a 7 = 0 := by omega
  by_cases h6 : a 6 = 1
  · exact b6Theta96Histogram_z11_a6_one a Q hc hs hm hQ hload hlarge hsmall hz7 h6
  · have hz6 : a 6 = 0 := by omega
    by_cases h52 : a 5 = 2
    · exact ⟨27,b6Theta96Histogram_case27 a Q hd ⟨hz7,hz6,h52⟩⟩
    · by_cases h51 : a 5 = 1
      · by_cases h4 : a 4 = 1
        · exact b6Theta96Histogram_z11_a5_one_a4_one a Q hc hs hm hQ hload hlarge hsmall hz7 hz6 h51 h4
        · exact b6Theta96Histogram_z11_a5_one_a4_rest a Q hc hs hm hQ hload hlarge hsmall hz7 hz6 h51 h4
      · have hz5 : a 5 = 0 := by omega
        by_cases h42 : a 4 = 2
        · exact b6Theta96Histogram_z11_a4_two a Q hc hs hm hQ hload hlarge hsmall hz7 hz6 hz5 h42
        · by_cases h41 : a 4 = 1
          · exact b6Theta96Histogram_z11_a4_one a Q hc hs hm hQ hload hlarge hsmall hz7 hz6 hz5 h41
          · exact b6Theta96Histogram_z11_a4_rest a Q hc hs hm hQ hload hlarge hsmall hz7 hz6 hz5 h42 h41
#print axioms Paper7MomentCounts.b6Theta96Histogram_z11_cover

theorem b6Theta96Histogram_z12_cover (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 12)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*12+2*Q = 84)
    (hQ : Q ≤ 12) (hload : 11 ≤ 12+Q)
    (hlarge : 2 ≤ Q → 12 ≤ 11) (hsmall : Q ≤ 1 → 12+Q ≤ 13) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 12 Q hs hm
  have hd : B6Theta96HistogramReducedData a 12 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  have hQ1 : Q ≤ 1 := by
    by_contra hn
    have hbad := hlarge (by omega)
    omega
  have hz7 : a 7 = 0 := by omega
  by_cases h6 : a 6 = 1
  · have hz5 : a 5 = 0 := by omega
    have hz4 : a 4 = 0 := by omega
    by_cases hq : Q = 1
    · exact ⟨48,b6Theta96Histogram_case48 a Q hd ⟨hz7,h6,hz5,hz4,hq⟩⟩
    · have hq0 : Q = 0 := by omega
      by_cases h3 : a 3 = 1
      · exact ⟨46,b6Theta96Histogram_case46 a Q hd ⟨hz7,h6,hz5,hz4,hq0,h3⟩⟩
      · have hz3 : a 3 = 0 := by omega
        exact ⟨47,b6Theta96Histogram_case47 a Q hd ⟨hz7,h6,hz5,hz4,hq0,hz3⟩⟩
  · have hz6 : a 6 = 0 := by omega
    by_cases h5 : a 5 = 1
    · have h4 : a 4 = 1 := by
        by_contra hn
        have hz4 : a 4 = 0 := by omega
        have hq1 : Q = 1 := by omega
        have hz1 : a 1 = 0 := by omega
        have hz2 : a 2 = 0 := by omega
        omega
      have hz3 : a 3 = 0 := by omega
      have hq1 : Q = 1 := by omega
      exact ⟨49,b6Theta96Histogram_case49 a Q hd ⟨hz7,hz6,h5,h4,hq1⟩⟩
    · have hz5 : a 5 = 0 := by omega
      exact ⟨50,b6Theta96Histogram_case50 a Q hd ⟨hz7,hz6,hz5⟩⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z12_cover

theorem b6Theta96Histogram_z13_cover (a : Fin 8 → ℕ) (Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = 13)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*13+2*Q = 84)
    (hQ : Q ≤ 13) (hload : 11 ≤ 13+Q)
    (hlarge : 2 ≤ Q → 13 ≤ 11) (hsmall : Q ≤ 1 → 13+Q ≤ 13) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hh := b6Theta96Histogram_halfMoment a 13 Q hs hm
  have hd : B6Theta96HistogramReducedData a 13 Q :=
    ⟨hc,hs,hh,hQ,hload,hlarge,hsmall⟩
  have hQ1 : Q ≤ 1 := by
    by_contra hn
    have hbad := hlarge (by omega)
    omega
  have hq : Q = 0 := by
    have hbound := hsmall hQ1
    omega
  have hz7 : a 7 = 0 := by omega
  have hz6 : a 6 = 0 := by
    by_contra hn
    have h6 : a 6 = 1 := by omega
    have hz5 : a 5 = 0 := by omega
    have hz4 : a 4 = 0 := by omega
    have hz3 : a 3 = 0 := by omega
    omega
  by_cases h5 : a 5 = 1
  · by_cases h4 : a 4 = 1
    · exact ⟨51,b6Theta96Histogram_case51 a Q hd ⟨hz7,hz6,h5,h4⟩⟩
    · have hz4 : a 4 = 0 := by omega
      exact ⟨52,b6Theta96Histogram_case52 a Q hd ⟨hz7,hz6,h5,hz4⟩⟩
  · have hz5 : a 5 = 0 := by omega
    have h42 : a 4 = 2 := by omega
    exact ⟨53,b6Theta96Histogram_case53 a Q hd ⟨hz7,hz6,hz5,h42⟩⟩
#print axioms Paper7MomentCounts.b6Theta96Histogram_z13_cover

theorem b6Theta96Histogram_linear_cover (a : Fin 8 → ℕ) (Z Q : ℕ)
    (hc : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6)
    (hs : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = Z)
    (hm : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+3*Z+2*Q = 84)
    (hlo : 7 ≤ Z) (hhi : Z ≤ 13) (hQ : Q ≤ Z) (hload : 11 ≤ Z+Q)
    (hlarge : 2 ≤ Q → Z ≤ 11) (hsmall : Q ≤ 1 → Z+Q ≤ 13) :
    ∃ j : Fin 54, a = b6Theta96Profile j ∧ Q = b6Theta96Q j := by
  have hz := b6Theta96Histogram_mass_cases Z hlo hhi
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b6Theta96Histogram_z7_cover a Q hc hs hm hQ hload hlarge hsmall
  · exact b6Theta96Histogram_z8_cover a Q hc hs hm hQ hload hlarge hsmall
  · exact b6Theta96Histogram_z9_cover a Q hc hs hm hQ hload hlarge hsmall
  · exact b6Theta96Histogram_z10_cover a Q hc hs hm hQ hload hlarge hsmall
  · exact b6Theta96Histogram_z11_cover a Q hc hs hm hQ hload hlarge hsmall
  · exact b6Theta96Histogram_z12_cover a Q hc hs hm hQ hload hlarge hsmall
  · exact b6Theta96Histogram_z13_cover a Q hc hs hm hQ hload hlarge hsmall
#print axioms Paper7MomentCounts.b6Theta96Histogram_linear_cover

theorem b6_theta96_histogram_cover (z : Fin 6 → ℕ) (Q : ℕ)
    (h : B6Theta96Data z Q) :
    ∃ j : Fin 54, ∃ e : Equiv.Perm (Fin 6),
      z = b6Theta96Nat j ∘ e ∧ Q = b6Theta96Q j := by
  let f : Fin 6 → Fin 8 := fun i => ⟨z i,by
    have hcap := b6_theta96_coordinate_le_seven z Q h i; omega⟩
  let a := finiteValueHistogram f
  have hc : (∑ v, a v) = 6 := finiteValueHistogram_total f
  have hs : (∑ v, a v * v.val) = ∑ i, z i :=
    finiteValueHistogram_sum_weight f (fun v => v.val)
  have hm : (∑ v, a v * v.val^2) + 3*(∑ i, z i) + 2*Q = 84 := by
    rw [finiteValueHistogram_sum_weight f (fun v => v.val^2)]
    exact h.2.2.2.2.2.2
  have hc' : a 0+a 1+a 2+a 3+a 4+a 5+a 6+a 7 = 6 := by
    simpa [Fin.sum_univ_succ,Nat.add_assoc] using hc
  have hs' : a 1+2*a 2+3*a 3+4*a 4+5*a 5+6*a 6+7*a 7 = ∑ i, z i := by
    simpa [Fin.sum_univ_succ,Nat.add_assoc,Nat.mul_comm] using hs
  have hm' : a 1+4*a 2+9*a 3+16*a 4+25*a 5+36*a 6+49*a 7+
      3*(∑ i, z i)+2*Q = 84 := by
    simpa [Fin.sum_univ_succ,Nat.add_assoc,Nat.mul_comm] using hm
  obtain ⟨j,hp,hq⟩ := b6Theta96Histogram_linear_cover a (∑ i, z i) Q hc' hs' hm'
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
  have heq : finiteValueHistogram f = finiteValueHistogram (b6Theta96Reference j) :=
    hp.trans (b6Theta96Reference_histogram j).symm
  obtain ⟨e,he⟩ := finiteValueHistogram_exists_perm (b6Theta96Reference j) f heq
  refine ⟨j,e,?_,hq⟩
  funext k
  exact congrArg Fin.val (congrFun he k)
#print axioms Paper7MomentCounts.b6_theta96_histogram_cover

end Paper7MomentCounts
