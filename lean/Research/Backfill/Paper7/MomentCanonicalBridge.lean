import Research.Backfill.Paper7.CanonicalRepresentativeCard
import Research.Backfill.Paper7.MomentBudgetEncoding

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
The imported canonical bridge and Stage 01 MomentBudgetEncoding remain uncompiled
candidates. This module proves the original B1/D2 canonical cardinalities equal,
without assuming numerical counts or identifying their different representative sets.
-/
set_option autoImplicit false
noncomputable section

namespace Paper7MomentCounts

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

theorem moment_reindex_sums (b : ℕ) (σ : Fin b → Fin b)
    (hσ : Function.Bijective σ) (x : PQ b) :
    pSum (reindex σ x) = pSum x ∧ qSum (reindex σ x) = qSum x := by
  exact ⟨hσ.sum_comp x.1, hσ.sum_comp x.2⟩

#print axioms Paper7MomentCounts.moment_reindex_sums

theorem moment_reindex_weight (b : ℕ) (σ : Fin b → Fin b)
    (hσ : Function.Bijective σ) (x : PQ b) :
    weight (reindex σ x) = weight x := by
  obtain ⟨hp, hq⟩ := moment_reindex_sums b σ hσ x
  simp only [weight, hp, hq]

#print axioms Paper7MomentCounts.moment_reindex_weight

theorem moment_reindex_theta (b : ℕ) (σ : Fin b → Fin b)
    (hσ : Function.Bijective σ) (x : PQ b) :
    theta (reindex σ x) = theta x :=
  hσ.sum_comp (fun i => thetaV (x.1 i) (x.2 i))

#print axioms Paper7MomentCounts.moment_reindex_theta

theorem momentPass_reindex_iff (cycleFilter loadBound countBound : Bool)
    (b N : ℕ) (σ : Fin b → Fin b) (hσ : Function.Bijective σ) (x : PQ b) :
    MomentPass cycleFilter loadBound countBound b N (reindex σ x) ↔
      MomentPass cycleFilter loadBound countBound b N x := by
  simp only [MomentPass, moment_reindex_weight b σ hσ x,
    moment_reindex_theta b σ hσ x,
    (moment_reindex_sums b σ hσ x).1, (moment_reindex_sums b σ hσ x).2]

#print axioms Paper7MomentCounts.momentPass_reindex_iff

theorem moment_budget_reindex_iff (b N : ℕ) (σ : Fin b → Fin b)
    (hσ : Function.Bijective σ) (x : PQ b) :
    Budget b N (reindex σ x) ↔ Budget b N x := by
  simp only [Budget, moment_reindex_weight b σ hσ x]

#print axioms Paper7MomentCounts.moment_budget_reindex_iff

theorem candB1_reindex_iff (b N : ℕ) (hb : 3 ≤ b) (σ : Fin b → Fin b)
    (hσ : IsDihedral b σ) (x : PQ b) :
    reindex σ x ∈ CandB1 b N ↔ x ∈ CandB1 b N := by
  have hbij := Paper7PruningCanonical.dihedral_bijective b hb σ hσ
  change (Budget b N (reindex σ x) ∧ MomentPass false true false b N (reindex σ x)) ↔
    (Budget b N x ∧ MomentPass false true false b N x)
  exact and_congr (moment_budget_reindex_iff b N σ hbij x)
    (momentPass_reindex_iff false true false b N σ hbij x)

#print axioms Paper7MomentCounts.candB1_reindex_iff

theorem budget_key_digit_bounds (b N : ℕ) (hN : N ≤ 49) (x : PQ b)
    (hx : Budget b N x) (i : Fin b) : x.1 i < 64 ∧ x.2 i < 1000 := by
  have hp : x.1 i ≤ pSum x :=
    Finset.single_le_sum (f := x.1) (fun j _ => Nat.zero_le (x.1 j))
      (Finset.mem_univ i)
  have hq : x.2 i ≤ qSum x :=
    Finset.single_le_sum (f := x.2) (fun j _ => Nat.zero_le (x.2 j))
      (Finset.mem_univ i)
  have hs := budget_sum_bounds b N x hx
  omega

#print axioms Paper7MomentCounts.budget_key_digit_bounds

theorem key1000_profile_injective_candB1 (b N : ℕ) (hN : N ≤ 49) :
    Set.InjOn (fun x : PQ b => fun i => key1000 (x.1 i) (x.2 i)) (CandB1 b N) := by
  intro x hx y hy h
  have hcoord (i : Fin b) : x.1 i = y.1 i ∧ x.2 i = y.2 i := by
    have hxi := budget_key_digit_bounds b N hN x hx.1 i
    have hyi := budget_key_digit_bounds b N hN y hy.1 i
    have hi := congrFun h i
    change key1000 (x.1 i) (x.2 i) = key1000 (y.1 i) (y.2 i) at hi
    have hq : x.2 i = y.2 i := by
      have hmod := congrArg (fun n : ℕ => n % 1000) hi
      simpa only [key1000, Nat.mul_add_mod_self_left,
        Nat.mod_eq_of_lt hxi.2, Nat.mod_eq_of_lt hyi.2] using hmod
    refine ⟨?_, hq⟩
    unfold key1000 at hi
    omega
  apply Prod.ext
  · funext i
    exact (hcoord i).1
  · funext i
    exact (hcoord i).2

#print axioms Paper7MomentCounts.key1000_profile_injective_candB1

theorem keyWeight_profile_injective_candB1 (b N : ℕ) (hN : N ≤ 49) :
    Set.InjOn (fun x : PQ b => fun i => keyWeight (x.1 i) (x.2 i)) (CandB1 b N) := by
  intro x hx y hy h
  have hcoord (i : Fin b) : x.1 i = y.1 i ∧ x.2 i = y.2 i := by
    have hxi := budget_key_digit_bounds b N hN x hx.1 i
    have hyi := budget_key_digit_bounds b N hN y hy.1 i
    have hi := congrFun h i
    change keyWeight (x.1 i) (x.2 i) = keyWeight (y.1 i) (y.2 i) at hi
    have hp : x.1 i = y.1 i := by
      have hmod := congrArg (fun n : ℕ => n % 64) hi
      simpa only [keyWeight, Nat.mul_add_mod_self_left,
        Nat.mod_eq_of_lt hxi.1, Nat.mod_eq_of_lt hyi.1] using hmod
    refine ⟨hp, ?_⟩
    unfold keyWeight at hi
    omega
  apply Prod.ext
  · funext i
    exact (hcoord i).1
  · funext i
    exact (hcoord i).2

#print axioms Paper7MomentCounts.keyWeight_profile_injective_candB1

theorem canonB1_ncard_eq_canonD2 (b N : ℕ) (hb : 3 ≤ b) (hN : N ≤ 49)
    (he : Even b) : (canonB1 b N).ncard = (canonD2 b N).ncard := by
  change (canonicalSubset (CandB1 b N) key1000 false).ncard =
    (canonicalSubset (CandD2 b N) keyWeight true).ncard
  rw [candD2_eq_candB1_of_even b N he]
  exact canonicalSubset_ncard_eq b hb (CandB1 b N) key1000 keyWeight false true
    (fun x hx σ hσ => (candB1_reindex_iff b N hb σ hσ x).mpr hx)
    (key1000_profile_injective_candB1 b N hN)
    (keyWeight_profile_injective_candB1 b N hN)

#print axioms Paper7MomentCounts.canonB1_ncard_eq_canonD2

end Paper7MomentCounts
