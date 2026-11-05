import Research.Backfill.Paper7.MomentB6HistogramFibres

/-! Source-only full Z10 histogram classification. The fourteen profiles are
conclusions of the original mass, square-moment and cardinality equations. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators

def b6TenReference : Fin 14 → Fin 6 → Fin 8 :=
  ![![7,1,1,1,0,0], ![6,4,0,0,0,0], ![6,3,1,0,0,0], ![6,2,2,0,0,0],
    ![6,2,1,1,0,0], ![6,1,1,1,1,0], ![5,5,0,0,0,0], ![5,4,1,0,0,0],
    ![5,3,2,0,0,0], ![5,3,1,1,0,0], ![5,2,2,1,0,0], ![4,4,2,0,0,0],
    ![4,4,1,1,0,0], ![4,3,3,0,0,0]]
#print axioms Paper7MomentCounts.b6TenReference

def b6TenProfile : Fin 14 → Fin 8 → ℕ :=
  ![![2,3,0,0,0,0,0,1], ![4,0,0,0,1,0,1,0], ![3,1,0,1,0,0,1,0],
    ![3,0,2,0,0,0,1,0], ![2,2,1,0,0,0,1,0], ![1,4,0,0,0,0,1,0],
    ![4,0,0,0,0,2,0,0], ![3,1,0,0,1,1,0,0], ![3,0,1,1,0,1,0,0],
    ![2,2,0,1,0,1,0,0], ![2,1,2,0,0,1,0,0], ![3,0,1,0,2,0,0,0],
    ![2,2,0,0,2,0,0,0], ![3,0,0,2,1,0,0,0]]
#print axioms Paper7MomentCounts.b6TenProfile

def b6TenProfileQ : Fin 14 → ℕ := ![1,1,4,5,6,7,2,6,8,9,10,9,10,10]
#print axioms Paper7MomentCounts.b6TenProfileQ

theorem b6TenReference_histogram :
    ∀ j : Fin 14, finiteValueHistogram (b6TenReference j) = b6TenProfile j := by
  decide
#print axioms Paper7MomentCounts.b6TenReference_histogram

theorem b6TenReference_moments : ∀ j : Fin 14,
    (∑ k, (b6TenReference j k).val) = 10 ∧
    1 ≤ b6TenProfileQ j ∧ b6TenProfileQ j ≤ 10 ∧
    (∑ k, (b6TenReference j k).val^2) + 2*b6TenProfileQ j = 54 := by
  decide
#print axioms Paper7MomentCounts.b6TenReference_moments

theorem b6TenProfile_injective : Function.Injective b6TenProfile := by
  decide
#print axioms Paper7MomentCounts.b6TenProfile_injective

def B6TenHistogramLinearData (a : Fin 8 → ℕ) (Q : ℕ) : Prop :=
  (a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 = 6) ∧
  (a 1 + 2*a 2 + 3*a 3 + 4*a 4 + 5*a 5 + 6*a 6 + 7*a 7 = 10) ∧
  (a 1 + 4*a 2 + 9*a 3 + 16*a 4 + 25*a 5 + 36*a 6 + 49*a 7 + 2*Q = 54) ∧
  1 ≤ Q ∧ Q ≤ 10
#print axioms Paper7MomentCounts.B6TenHistogramLinearData

theorem b6TenHistogram_case0 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 1) :
    a = b6TenProfile 0 ∧ Q = b6TenProfileQ 0 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case0

theorem b6TenHistogram_case1 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 1)
    (_h4 : a 4 = 1) : a = b6TenProfile 1 ∧ Q = b6TenProfileQ 1 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case1

theorem b6TenHistogram_case2 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 1)
    (_h4 : a 4 ≠ 1) (_h3 : a 3 = 1) : a = b6TenProfile 2 ∧ Q = b6TenProfileQ 2 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case2

theorem b6TenHistogram_case3 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 1)
    (_h4 : a 4 ≠ 1) (_h3 : a 3 ≠ 1) (_h2 : a 2 = 2) :
    a = b6TenProfile 3 ∧ Q = b6TenProfileQ 3 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case3

theorem b6TenHistogram_case4 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 1)
    (_h4 : a 4 ≠ 1) (_h3 : a 3 ≠ 1) (_h22 : a 2 ≠ 2) (_h21 : a 2 = 1) :
    a = b6TenProfile 4 ∧ Q = b6TenProfileQ 4 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case4

theorem b6TenHistogram_case5 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 1)
    (_h4 : a 4 ≠ 1) (_h3 : a 3 ≠ 1) (_h22 : a 2 ≠ 2) (_h21 : a 2 ≠ 1) :
    a = b6TenProfile 5 ∧ Q = b6TenProfileQ 5 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case5

theorem b6TenHistogram_case6 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 0)
    (_h5 : a 5 = 2) : a = b6TenProfile 6 ∧ Q = b6TenProfileQ 6 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case6

theorem b6TenHistogram_case7 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 0)
    (_h52 : a 5 ≠ 2) (_h51 : a 5 = 1) (_h4 : a 4 = 1) :
    a = b6TenProfile 7 ∧ Q = b6TenProfileQ 7 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case7

theorem b6TenHistogram_case8 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 0)
    (_h52 : a 5 ≠ 2) (_h51 : a 5 = 1) (_h4 : a 4 ≠ 1) (_h3 : a 3 = 1)
    (_h2 : a 2 = 1) : a = b6TenProfile 8 ∧ Q = b6TenProfileQ 8 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case8

theorem b6TenHistogram_case9 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 0)
    (_h52 : a 5 ≠ 2) (_h51 : a 5 = 1) (_h4 : a 4 ≠ 1) (_h3 : a 3 = 1)
    (_h2 : a 2 ≠ 1) : a = b6TenProfile 9 ∧ Q = b6TenProfileQ 9 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case9

theorem b6TenHistogram_case10 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 0)
    (_h52 : a 5 ≠ 2) (_h51 : a 5 = 1) (_h4 : a 4 ≠ 1) (_h3 : a 3 ≠ 1) :
    a = b6TenProfile 10 ∧ Q = b6TenProfileQ 10 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case10

theorem b6TenHistogram_case11 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 0)
    (_h5 : a 5 = 0) (_h4 : a 4 = 2) (_h2 : a 2 = 1) :
    a = b6TenProfile 11 ∧ Q = b6TenProfileQ 11 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case11

theorem b6TenHistogram_case12 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 0)
    (_h5 : a 5 = 0) (_h4 : a 4 = 2) (_h2 : a 2 ≠ 1) :
    a = b6TenProfile 12 ∧ Q = b6TenProfileQ 12 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case12

theorem b6TenHistogram_case13 (a : Fin 8 → ℕ) (Q : ℕ)
    (h : B6TenHistogramLinearData a Q) (_h7 : a 7 = 0) (_h6 : a 6 = 0)
    (_h5 : a 5 = 0) (_h4 : a 4 ≠ 2) : a = b6TenProfile 13 ∧ Q = b6TenProfileQ 13 := by
  rcases h with ⟨hc,hs,hm,hlo,hhi⟩
  constructor
  · funext v
    fin_cases v <;> norm_num [b6TenProfile] <;> omega
  · norm_num [b6TenProfileQ]
    omega
#print axioms Paper7MomentCounts.b6TenHistogram_case13

theorem b6TenHistogram_linear_cover (a : Fin 8 → ℕ) (Q : ℕ)
    (hcard : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 = 6)
    (hmass : a 1 + 2*a 2 + 3*a 3 + 4*a 4 + 5*a 5 + 6*a 6 + 7*a 7 = 10)
    (hmoment : a 1 + 4*a 2 + 9*a 3 + 16*a 4 + 25*a 5 + 36*a 6 + 49*a 7 + 2*Q = 54)
    (hQ1 : 1 ≤ Q) (hQ10 : Q ≤ 10) :
    ∃ j : Fin 14, a = b6TenProfile j ∧ Q = b6TenProfileQ j := by
  have h : B6TenHistogramLinearData a Q := ⟨hcard,hmass,hmoment,hQ1,hQ10⟩
  by_cases h7 : a 7 = 1
  · exact ⟨0,b6TenHistogram_case0 a Q h h7⟩
  · have hz7 : a 7 = 0 := by omega
    by_cases h6 : a 6 = 1
    · by_cases h4 : a 4 = 1
      · exact ⟨1,b6TenHistogram_case1 a Q h hz7 h6 h4⟩
      · by_cases h3 : a 3 = 1
        · exact ⟨2,b6TenHistogram_case2 a Q h hz7 h6 h4 h3⟩
        · by_cases h22 : a 2 = 2
          · exact ⟨3,b6TenHistogram_case3 a Q h hz7 h6 h4 h3 h22⟩
          · by_cases h21 : a 2 = 1
            · exact ⟨4,b6TenHistogram_case4 a Q h hz7 h6 h4 h3 h22 h21⟩
            · exact ⟨5,b6TenHistogram_case5 a Q h hz7 h6 h4 h3 h22 h21⟩
    · have hz6 : a 6 = 0 := by omega
      by_cases h52 : a 5 = 2
      · exact ⟨6,b6TenHistogram_case6 a Q h hz7 hz6 h52⟩
      · by_cases h51 : a 5 = 1
        · by_cases h4 : a 4 = 1
          · exact ⟨7,b6TenHistogram_case7 a Q h hz7 hz6 h52 h51 h4⟩
          · by_cases h3 : a 3 = 1
            · by_cases h2 : a 2 = 1
              · exact ⟨8,b6TenHistogram_case8 a Q h hz7 hz6 h52 h51 h4 h3 h2⟩
              · exact ⟨9,b6TenHistogram_case9 a Q h hz7 hz6 h52 h51 h4 h3 h2⟩
            · exact ⟨10,b6TenHistogram_case10 a Q h hz7 hz6 h52 h51 h4 h3⟩
        · have hz5 : a 5 = 0 := by omega
          by_cases h42 : a 4 = 2
          · by_cases h2 : a 2 = 1
            · exact ⟨11,b6TenHistogram_case11 a Q h hz7 hz6 hz5 h42 h2⟩
            · exact ⟨12,b6TenHistogram_case12 a Q h hz7 hz6 hz5 h42 h2⟩
          · exact ⟨13,b6TenHistogram_case13 a Q h hz7 hz6 hz5 h42⟩
#print axioms Paper7MomentCounts.b6TenHistogram_linear_cover

def b6TenFiniteCapacity (z : Fin 6 → ℕ) (hcap : ∀ k, z k ≤ 7) : Fin 6 → Fin 8 :=
  fun k => ⟨z k,by have h := hcap k; omega⟩
#print axioms Paper7MomentCounts.b6TenFiniteCapacity

theorem b6_ten_guard_histogram_cover (z : Fin 6 → ℕ) (Q : ℕ)
    (hZ : (∑ k, z k) = 10) (hQ : Q ≤ 10) (hg : b6TenMomentGuard z Q) :
    ∃ j : Fin 14, ∃ e : Equiv.Perm (Fin 6),
      z = (fun k => (b6TenReference j (e k)).val) ∧ Q = b6TenProfileQ j := by
  let f := b6TenFiniteCapacity z (b6_ten_guard_coordinate_le_seven z Q hQ hg)
  let a := finiteValueHistogram f
  have hc : (∑ v, a v) = 6 := finiteValueHistogram_total f
  have hm : (∑ v, a v * v.val) = 10 := by
    have h := finiteValueHistogram_sum_weight f (fun v => v.val)
    exact h.trans hZ
  have hs : (∑ v, a v * v.val^2) + 2*Q = 54 := by
    have h := finiteValueHistogram_sum_weight f (fun v => v.val^2)
    have he : (∑ k, z k^2) + 2*Q = 54 := by exact_mod_cast hg.2
    exact (congrArg (fun u => u + 2*Q) h).trans he
  have hc' : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 = 6 := by
    simpa [Fin.sum_univ_succ,Nat.add_assoc] using hc
  have hm' : a 1 + 2*a 2 + 3*a 3 + 4*a 4 + 5*a 5 + 6*a 6 + 7*a 7 = 10 := by
    simpa [Fin.sum_univ_succ,Nat.add_assoc,Nat.mul_comm] using hm
  have hs' : a 1 + 4*a 2 + 9*a 3 + 16*a 4 + 25*a 5 + 36*a 6 + 49*a 7 + 2*Q = 54 := by
    simpa [Fin.sum_univ_succ,Nat.add_assoc,Nat.mul_comm] using hs
  obtain ⟨j,hprof,hq⟩ := b6TenHistogram_linear_cover a Q hc' hm' hs' hg.1 hQ
  have heq : finiteValueHistogram f = finiteValueHistogram (b6TenReference j) :=
    hprof.trans (b6TenReference_histogram j).symm
  obtain ⟨e,he⟩ := finiteValueHistogram_exists_perm (b6TenReference j) f heq
  refine ⟨j,e,?_,hq⟩
  funext k
  exact congrArg Fin.val (congrFun he k)
#print axioms Paper7MomentCounts.b6_ten_guard_histogram_cover

end Paper7MomentCounts
