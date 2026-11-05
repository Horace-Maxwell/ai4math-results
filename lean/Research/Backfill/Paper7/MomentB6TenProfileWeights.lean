import Research.Backfill.Paper7.MomentB6TenProfiles
import Research.Backfill.Paper7.MomentB4RowSymmetry

/-! Source-only actual bounded-q weights for fourteen full Z10 profiles.
Each finite certificate retains every assignment of the five non-pivot
coordinates and both inequalities for the recovered pivot. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators

def b6TenReferenceNat (j : Fin 14) (k : Fin 6) : ℕ := (b6TenReference j k).val
#print axioms Paper7MomentCounts.b6TenReferenceNat

def b6TenProfileWeight : Fin 14 → ℕ := ![4,2,8,9,12,15,3,9,6,4,1,3,1,1]
#print axioms Paper7MomentCounts.b6TenProfileWeight

def b6TenTailGuard (j : Fin 14)
    (a : (k : {k : Fin 6 // k ≠ 0}) → Fin (b6TenReferenceNat j k.val + 1)) : Bool :=
  decide ((∑ k, boundedTailValue 6 (b6TenReferenceNat j) 0 a k) ≤
    min (b6TenProfileQ j) (10-b6TenProfileQ j)) &&
  decide (min (b6TenProfileQ j) (10-b6TenProfileQ j) ≤
    b6TenReferenceNat j 0 + (∑ k, boundedTailValue 6 (b6TenReferenceNat j) 0 a k))
#print axioms Paper7MomentCounts.b6TenTailGuard

def b6TenTailSum (j : Fin 14) : ℕ :=
  ∑ a : (k : {k : Fin 6 // k ≠ 0}) → Fin (b6TenReferenceNat j k.val + 1),
    if b6TenTailGuard j a then 1 else 0
#print axioms Paper7MomentCounts.b6TenTailSum

theorem b6TenTailSum_0 : b6TenTailSum 0 = 4 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_0

theorem b6TenTailSum_1 : b6TenTailSum 1 = 2 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_1

theorem b6TenTailSum_2 : b6TenTailSum 2 = 8 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_2

theorem b6TenTailSum_3 : b6TenTailSum 3 = 9 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_3

theorem b6TenTailSum_4 : b6TenTailSum 4 = 12 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_4

theorem b6TenTailSum_5 : b6TenTailSum 5 = 15 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_5

theorem b6TenTailSum_6 : b6TenTailSum 6 = 3 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_6

theorem b6TenTailSum_7 : b6TenTailSum 7 = 9 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_7

theorem b6TenTailSum_8 : b6TenTailSum 8 = 6 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_8

theorem b6TenTailSum_9 : b6TenTailSum 9 = 4 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_9

theorem b6TenTailSum_10 : b6TenTailSum 10 = 1 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_10

theorem b6TenTailSum_11 : b6TenTailSum 11 = 3 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_11

theorem b6TenTailSum_12 : b6TenTailSum 12 = 1 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_12

theorem b6TenTailSum_13 : b6TenTailSum 13 = 1 := by decide
#print axioms Paper7MomentCounts.b6TenTailSum_13

theorem b6TenTailSum_values (j : Fin 14) : b6TenTailSum j = b6TenProfileWeight j := by
  fin_cases j
  · exact b6TenTailSum_0
  · exact b6TenTailSum_1
  · exact b6TenTailSum_2
  · exact b6TenTailSum_3
  · exact b6TenTailSum_4
  · exact b6TenTailSum_5
  · exact b6TenTailSum_6
  · exact b6TenTailSum_7
  · exact b6TenTailSum_8
  · exact b6TenTailSum_9
  · exact b6TenTailSum_10
  · exact b6TenTailSum_11
  · exact b6TenTailSum_12
  · exact b6TenTailSum_13
#print axioms Paper7MomentCounts.b6TenTailSum_values

theorem b6TenReference_weight (j : Fin 14) :
    Paper7MomentDP.boundedQDP 6 (b6TenReferenceNat j) (b6TenProfileQ j) =
      b6TenProfileWeight j := by
  classical
  have hm := b6TenReference_moments j
  rw [(b6_total_ten_half_Q_weight (b6TenReferenceNat j) hm.1
    (b6TenProfileQ j) hm.2.2.1).1]
  rw [boundedQDP_sliced_sum 6 (b6TenReferenceNat j) 0]
  calc
    (∑ a : (k : {k : Fin 6 // k ≠ 0}) → Fin (b6TenReferenceNat j k.val + 1),
      if BoundedTailSlice 6 (b6TenReferenceNat j) 0
        (min (b6TenProfileQ j) (10-b6TenProfileQ j)) a then 1 else 0)
        = b6TenTailSum j := by
      apply Finset.sum_congr rfl
      intro a _ha
      simp [BoundedTailSlice,b6TenTailGuard]
    _ = b6TenProfileWeight j := b6TenTailSum_values j
#print axioms Paper7MomentCounts.b6TenReference_weight

theorem b6TenHistogram_member_moments (j : Fin 14)
    (g : FiniteHistogramFiber (b6TenReference j)) :
    (∑ k, (g.val k).val) = 10 ∧
      (∑ k, ((g.val k).val : ℤ)^2) + 2*(b6TenProfileQ j : ℤ) = 54 := by
  obtain ⟨e,he⟩ := finiteValueHistogram_exists_perm (b6TenReference j) g.val g.property
  have hm := b6TenReference_moments j
  constructor
  · rw [he]
    exact (Equiv.sum_comp e (fun k => (b6TenReference j k).val)).trans hm.1
  · have hn : (∑ k, (g.val k).val^2) + 2*b6TenProfileQ j = 54 := by
      rw [he]
      change (∑ k, (b6TenReference j (e k)).val ^ 2) + 2 * b6TenProfileQ j = 54
      rw [Equiv.sum_comp e (fun k => (b6TenReference j k).val^2)]
      exact hm.2.2.2
    exact_mod_cast hn
#print axioms Paper7MomentCounts.b6TenHistogram_member_moments

theorem b6TenHistogram_member_accept (j : Fin 14)
    (g : FiniteHistogramFiber (b6TenReference j)) :
    b6ZQAccept (fun k => (g.val k).val) (b6TenProfileQ j) := by
  have hm := b6TenHistogram_member_moments j g
  have hr := b6TenReference_moments j
  apply (b6_zq_accept_total_ten_iff _ _ hm.1 hr.2.2.1).mpr
  exact ⟨hr.2.1,hm.2⟩
#print axioms Paper7MomentCounts.b6TenHistogram_member_accept

theorem b6TenHistogram_member_weight (j : Fin 14)
    (g : FiniteHistogramFiber (b6TenReference j)) :
    Paper7MomentDP.boundedQDP 6 (fun k => (g.val k).val) (b6TenProfileQ j) =
      b6TenProfileWeight j := by
  obtain ⟨e,he⟩ := finiteValueHistogram_exists_perm (b6TenReference j) g.val g.property
  have hn : (fun k => (g.val k).val) = b6TenReferenceNat j ∘ e := by
    funext k
    exact congrArg Fin.val (congrFun he k)
  rw [hn,Paper7MomentReduction.boundedQDP_comp_perm]
  exact b6TenReference_weight j
#print axioms Paper7MomentCounts.b6TenHistogram_member_weight

end Paper7MomentCounts
