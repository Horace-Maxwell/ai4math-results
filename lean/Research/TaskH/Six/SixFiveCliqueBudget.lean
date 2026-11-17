import Research.TaskH.Six.SixFiveCliqueSets
import Research.TaskH.Six.EqualityDegree

/-! Actual six-vertex degree and cycle-incidence budgets. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem six_cross_neighbors_double_count (S : Finset V) :
    (∑ v ∈ S, (packingNeighborsIn G Sᶜ v).card) =
      ∑ v ∈ Sᶜ, (packingNeighborsIn G S v).card := by
  classical
  calc
    _ = ∑ y ∈ Sᶜ, (S.filter (fun x => G.Adj x y)).card := by
      convert FiniteBudget.relation_double_count S Sᶜ G.Adj using 1 <;>
        apply Finset.sum_congr rfl
      all_goals
        intro v _
        congr 1
        ext x
        simp only [packingNeighborsIn, Finset.mem_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      ext x
      simp only [Finset.mem_filter, packingNeighborsIn, G.adj_comm]

theorem six_sum_degrees_on_set (S : Finset V) :
    (∑ v ∈ S, G.degree v) =
      (∑ v ∈ S, (packingNeighborsIn G S v).card) +
        ∑ v ∈ Sᶜ, (packingNeighborsIn G S v).card := by
  calc
    _ = ∑ v ∈ S, ((packingNeighborsIn G S v).card + (packingNeighborsIn G Sᶜ v).card) :=
      Finset.sum_congr rfl (fun v _ => (packingNeighborsIn_partition S v).symm)
    _ = _ := by rw [Finset.sum_add_distrib, six_cross_neighbors_double_count]

omit [Fintype V] in
theorem six_internal_degree_sum_le_thirty (S : Finset V) (hS : S.card = 6) :
    (∑ v ∈ S, (packingNeighborsIn G S v).card) ≤ 30 := by
  classical
  have hrow : ∀ v ∈ S, (packingNeighborsIn G S v).card ≤ 5 := by
    intro v hv
    have hsub : packingNeighborsIn G S v ⊆ S.erase v := by
      intro x hx
      have hh := Finset.mem_filter.mp hx
      exact Finset.mem_erase.mpr ⟨hh.2.ne.symm, hh.1⟩
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem hv, hS] at hh
  calc
    _ ≤ ∑ _v ∈ S, 5 := Finset.sum_le_sum hrow
    _ = 30 := by simp [hS]

theorem sparse_six_set_degree_bound (S : Finset V) (hS : S.card = 6)
    (hout : ∀ v ∈ Sᶜ, (packingNeighborsIn G S v).card ≤ 1) :
    (∑ v ∈ S, G.degree v) ≤ 30 + Sᶜ.card := by
  rw [six_sum_degrees_on_set]
  have hin := six_internal_degree_sum_le_thirty (G := G) S hS
  have hex : (∑ v ∈ Sᶜ, (packingNeighborsIn G S v).card) ≤ Sᶜ.card := by
    calc
      _ ≤ ∑ _v ∈ Sᶜ, 1 := Finset.sum_le_sum hout
      _ = _ := by simp
  omega

theorem six_singleton_budget_on_set
    (hsingle : ∀ v : V, 60 * (12 - G.degree v) ≤
      (TaskH.modCyclesThrough 6 G v).ncard) (S : Finset V) :
    720 * S.card ≤ (∑ v ∈ S, cycleDegree G v) + 60 * ∑ v ∈ S, G.degree v := by
  have hrow : ∀ v : V, 720 ≤ cycleDegree G v + 60 * G.degree v := by
    intro v
    have hh := hsingle v
    rw [← cycleDegree_eq_ncard] at hh
    omega
  calc
    _ = ∑ _v ∈ S, 720 := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ S, (cycleDegree G v + 60 * G.degree v) :=
      Finset.sum_le_sum (fun v _ => hrow v)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem six_set_incidence_degree_budget (hs : ShortSixCycles G)
    (hc : modCycleCount 6 G = 420)
    (h13 : ∀ v : V, 61 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 60 * (12 - G.degree v) ≤
      (TaskH.modCyclesThrough 6 G v).ncard)
    (S : Finset V) (hS : S.card = 6) (D : ℕ)
    (hD : (∑ v ∈ S, G.degree v) ≤ D) :
    4320 + 61 * Sᶜ.card ≤ 2520 + 60 * D := by
  have hin := six_singleton_budget_on_set hsingle S
  rw [hS] at hin
  have hout : 61 * Sᶜ.card ≤ ∑ v ∈ Sᶜ, cycleDegree G v := by
    calc
      _ = ∑ _v ∈ Sᶜ, 61 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => h13 v)
  have hp := Finset.sum_add_sum_compl S (cycleDegree G)
  rw [sum_cycleDegree_eq_2520 hs hc] at hp
  have hm := Nat.mul_le_mul_left 60 hD
  omega

theorem no_sparse_six_vertex_set (hs : ShortSixCycles G)
    (hc : modCycleCount 6 G = 420) (hn : 7 ≤ Fintype.card V)
    (h13 : ∀ v : V, 61 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 60 * (12 - G.degree v) ≤
      (TaskH.modCyclesThrough 6 G v).ncard)
    (S : Finset V) (hS : S.card = 6)
    (hout : ∀ v ∈ Sᶜ, (packingNeighborsIn G S v).card ≤ 1) : False := by
  have hd := sparse_six_set_degree_bound S hS hout
  have hb := six_set_incidence_degree_budget hs hc h13 hsingle S hS
    (30 + Sᶜ.card) hd
  have hcard := Finset.card_add_card_compl S
  rw [hS] at hcard
  omega

theorem critical_no_sparse_six_set (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hc : modCycleCount 6 G = 420)
    (S : Finset V) (hS : S.card = 6)
    (hout : ∀ v ∈ Sᶜ, (packingNeighborsIn G S v).card ≤ 1) : False :=
  no_sparse_six_vertex_set hs hc (critical_six_card_ge_seven hcrit)
    (fun v => critical_sixty_one_le_cycleDegree hcrit hs v)
    (fun v => critical_singleton_cycle_bound hcrit hs v) S hS hout

end TaskH.Six

#print axioms TaskH.Six.six_cross_neighbors_double_count
#print axioms TaskH.Six.six_sum_degrees_on_set
#print axioms TaskH.Six.six_internal_degree_sum_le_thirty
#print axioms TaskH.Six.sparse_six_set_degree_bound
#print axioms TaskH.Six.six_singleton_budget_on_set
#print axioms TaskH.Six.six_set_incidence_degree_budget
#print axioms TaskH.Six.no_sparse_six_vertex_set
#print axioms TaskH.Six.critical_no_sparse_six_set
