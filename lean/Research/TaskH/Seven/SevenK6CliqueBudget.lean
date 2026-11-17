import Research.TaskH.Seven.SevenK6CliqueSets
import Research.TaskH.Seven.SingletonCycles
import Research.TaskH.Seven.SevenIncidence
import Research.TaskH.Seven.SevenNoncompleteDegree

/-! Actual seven-vertex degree and cycle-incidence budgets. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem seven_cross_neighbors_double_count (S : Finset V) :
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

theorem seven_sum_degrees_on_set (S : Finset V) :
    (∑ v ∈ S, G.degree v) =
      (∑ v ∈ S, (packingNeighborsIn G S v).card) +
        ∑ v ∈ Sᶜ, (packingNeighborsIn G S v).card := by
  calc
    _ = ∑ v ∈ S, ((packingNeighborsIn G S v).card + (packingNeighborsIn G Sᶜ v).card) :=
      Finset.sum_congr rfl (fun v _ => (packingNeighborsIn_partition S v).symm)
    _ = _ := by rw [Finset.sum_add_distrib, seven_cross_neighbors_double_count]

omit [Fintype V] in
theorem seven_internal_degree_sum_le_forty_two (S : Finset V) (hS : S.card = 7) :
    (∑ v ∈ S, (packingNeighborsIn G S v).card) ≤ 42 := by
  classical
  have hrow : ∀ v ∈ S, (packingNeighborsIn G S v).card ≤ 6 := by
    intro v hv
    have hsub : packingNeighborsIn G S v ⊆ S.erase v := by
      intro x hx
      have hh := Finset.mem_filter.mp hx
      exact Finset.mem_erase.mpr ⟨hh.2.ne.symm, hh.1⟩
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem hv, hS] at hh
  calc
    _ ≤ ∑ _v ∈ S, 6 := Finset.sum_le_sum hrow
    _ = 42 := by simp [hS]

theorem sparse_seven_set_degree_bound (S : Finset V) (hS : S.card = 7)
    (hout : ∀ v ∈ Sᶜ, (packingNeighborsIn G S v).card ≤ 1) :
    (∑ v ∈ S, G.degree v) ≤ 42 + Sᶜ.card := by
  rw [seven_sum_degrees_on_set]
  have hin := seven_internal_degree_sum_le_forty_two (G := G) S hS
  have hex : (∑ v ∈ Sᶜ, (packingNeighborsIn G S v).card) ≤ Sᶜ.card := by
    calc
      _ ≤ ∑ _v ∈ Sᶜ, 1 := Finset.sum_le_sum hout
      _ = _ := by simp
  omega

theorem seven_singleton_budget_on_set
    (hsingle : ∀ v : V, 360 * (14 - G.degree v) ≤
      (TaskH.modCyclesThrough 7 G v).ncard) (S : Finset V) :
    5040 * S.card ≤ (∑ v ∈ S, cycleDegree G v) + 360 * ∑ v ∈ S, G.degree v := by
  have hrow : ∀ v : V, 5040 ≤ cycleDegree G v + 360 * G.degree v := by
    intro v
    have hh := hsingle v
    rw [← cycleDegree_eq_ncard] at hh
    omega
  calc
    _ = ∑ _v ∈ S, 5040 := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ S, (cycleDegree G v + 360 * G.degree v) :=
      Finset.sum_le_sum (fun v _ => hrow v)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem seven_set_incidence_degree_budget (hs : ShortSevenCycles G)
    (hc : modCycleCount 7 G = 2880)
    (h13 : ∀ v : V, 361 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 360 * (14 - G.degree v) ≤
      (TaskH.modCyclesThrough 7 G v).ncard)
    (S : Finset V) (hS : S.card = 7) (D : ℕ)
    (hD : (∑ v ∈ S, G.degree v) ≤ D) :
    35280 + 361 * Sᶜ.card ≤ 20160 + 360 * D := by
  have hin := seven_singleton_budget_on_set hsingle S
  rw [hS] at hin
  have hout : 361 * Sᶜ.card ≤ ∑ v ∈ Sᶜ, cycleDegree G v := by
    calc
      _ = ∑ _v ∈ Sᶜ, 361 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => h13 v)
  have hp := Finset.sum_add_sum_compl S (cycleDegree G)
  rw [sum_cycleDegree_eq_20160 hs hc] at hp
  have hm := Nat.mul_le_mul_left 360 hD
  omega

theorem no_sparse_seven_vertex_set (hs : ShortSevenCycles G)
    (hc : modCycleCount 7 G = 2880) (hn : 8 ≤ Fintype.card V)
    (h13 : ∀ v : V, 361 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 360 * (14 - G.degree v) ≤
      (TaskH.modCyclesThrough 7 G v).ncard)
    (S : Finset V) (hS : S.card = 7)
    (hout : ∀ v ∈ Sᶜ, (packingNeighborsIn G S v).card ≤ 1) : False := by
  have hd := sparse_seven_set_degree_bound S hS hout
  have hb := seven_set_incidence_degree_budget hs hc h13 hsingle S hS
    (42 + Sᶜ.card) hd
  have hcard := Finset.card_add_card_compl S
  rw [hS] at hcard
  omega

theorem critical_no_sparse_seven_set (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hc : modCycleCount 7 G = 2880)
    (S : Finset V) (hS : S.card = 7)
    (hout : ∀ v ∈ Sᶜ, (packingNeighborsIn G S v).card ≤ 1) : False :=
  no_sparse_seven_vertex_set hs hc (critical_seven_card_ge_eight hcrit)
    (fun v => critical_three_hundred_sixty_one_le_cycleDegree hcrit hs v)
    (fun v => critical_singleton_cycle_bound hcrit hs v) S hS hout

end TaskH.Seven

#print axioms TaskH.Seven.seven_cross_neighbors_double_count
#print axioms TaskH.Seven.seven_sum_degrees_on_set
#print axioms TaskH.Seven.seven_internal_degree_sum_le_forty_two
#print axioms TaskH.Seven.sparse_seven_set_degree_bound
#print axioms TaskH.Seven.seven_singleton_budget_on_set
#print axioms TaskH.Seven.seven_set_incidence_degree_budget
#print axioms TaskH.Seven.no_sparse_seven_vertex_set
#print axioms TaskH.Seven.critical_no_sparse_seven_set
