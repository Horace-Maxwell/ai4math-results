import Research.TaskH.Five.FiveIncidence

/-! Actual degree and cycle-incidence budgets on a five-vertex set. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def neighborsIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    Finset V := S.filter (G.Adj v)

theorem neighborsIn_partition (S : Finset V) (v : V) :
    (neighborsIn G S v).card + (neighborsIn G Sᶜ v).card = G.degree v := by
  classical
  have h1 : (G.neighborFinset v).filter (fun x => x ∈ S) = neighborsIn G S v := by
    ext x
    simp [neighborsIn, G.mem_neighborFinset, and_comm]
  have h2 : (G.neighborFinset v).filter (fun x => x ∉ S) = neighborsIn G Sᶜ v := by
    ext x
    simp [neighborsIn, G.mem_neighborFinset, and_comm]
  have hh := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset v) (fun x => x ∈ S)
  rwa [h1, h2, G.card_neighborFinset_eq_degree] at hh

theorem cross_neighbors_double_count (S : Finset V) :
    (∑ v ∈ S, (neighborsIn G Sᶜ v).card) =
      ∑ v ∈ Sᶜ, (neighborsIn G S v).card := by
  classical
  calc
    _ = ∑ y ∈ Sᶜ, (S.filter (fun x => G.Adj x y)).card := by
      convert FiniteBudget.relation_double_count S Sᶜ G.Adj using 1 <;>
        apply Finset.sum_congr rfl
      all_goals
        intro v _
        congr 1
        ext x
        simp only [neighborsIn, Finset.mem_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      ext x
      simp only [Finset.mem_filter, neighborsIn, G.adj_comm]

theorem sum_degrees_on_set (S : Finset V) :
    (∑ v ∈ S, G.degree v) =
      (∑ v ∈ S, (neighborsIn G S v).card) +
        ∑ v ∈ Sᶜ, (neighborsIn G S v).card := by
  calc
    _ = ∑ v ∈ S, ((neighborsIn G S v).card + (neighborsIn G Sᶜ v).card) :=
      Finset.sum_congr rfl (fun v _ => (neighborsIn_partition S v).symm)
    _ = _ := by rw [Finset.sum_add_distrib, cross_neighbors_double_count]

omit [Fintype V] in
theorem internal_degree_sum_le_twenty (S : Finset V) (hS : S.card = 5) :
    (∑ v ∈ S, (neighborsIn G S v).card) ≤ 20 := by
  classical
  have hrow : ∀ v ∈ S, (neighborsIn G S v).card ≤ 4 := by
    intro v hv
    have hsub : neighborsIn G S v ⊆ S.erase v := by
      intro x hx
      have hh := Finset.mem_filter.mp hx
      exact Finset.mem_erase.mpr ⟨hh.2.ne.symm, hh.1⟩
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem hv, hS] at hh
  calc
    _ ≤ ∑ _v ∈ S, 4 := Finset.sum_le_sum hrow
    _ = 20 := by simp [hS]

theorem sparse_five_set_degree_bound (S : Finset V) (hS : S.card = 5)
    (hout : ∀ v ∈ Sᶜ, (neighborsIn G S v).card ≤ 1) :
    (∑ v ∈ S, G.degree v) ≤ 20 + Sᶜ.card := by
  rw [sum_degrees_on_set]
  have hin := internal_degree_sum_le_twenty (G := G) S hS
  have hex : (∑ v ∈ Sᶜ, (neighborsIn G S v).card) ≤ Sᶜ.card := by
    calc
      _ ≤ ∑ _v ∈ Sᶜ, 1 := Finset.sum_le_sum hout
      _ = _ := by simp
  omega

theorem singleton_budget_on_set
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard) (S : Finset V) :
    120 * S.card ≤ (∑ v ∈ S, cycleDegree G v) + 12 * ∑ v ∈ S, G.degree v := by
  have hrow : ∀ v : V, 120 ≤ cycleDegree G v + 12 * G.degree v := by
    intro v
    have hh := hsingle v
    rw [← cycleDegree_eq_ncard] at hh
    omega
  calc
    _ = ∑ _v ∈ S, 120 := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ S, (cycleDegree G v + 12 * G.degree v) :=
      Finset.sum_le_sum (fun v _ => hrow v)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem five_set_incidence_degree_budget (hs : ShortFiveCycles G)
    (hc : modCycleCount 5 G = 72)
    (h13 : ∀ v : V, 13 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard)
    (S : Finset V) (hS : S.card = 5) (D : ℕ)
    (hD : (∑ v ∈ S, G.degree v) ≤ D) :
    600 + 13 * Sᶜ.card ≤ 360 + 12 * D := by
  have hin := singleton_budget_on_set hsingle S
  rw [hS] at hin
  have hout : 13 * Sᶜ.card ≤ ∑ v ∈ Sᶜ, cycleDegree G v := by
    calc
      _ = ∑ _v ∈ Sᶜ, 13 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => h13 v)
  have hp := Finset.sum_add_sum_compl S (cycleDegree G)
  rw [sum_cycleDegree_eq_360 hs hc] at hp
  have hm := Nat.mul_le_mul_left 12 hD
  omega

theorem no_sparse_five_vertex_set (hs : ShortFiveCycles G)
    (hc : modCycleCount 5 G = 72) (hn : 6 ≤ Fintype.card V)
    (h13 : ∀ v : V, 13 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard)
    (S : Finset V) (hS : S.card = 5)
    (hout : ∀ v ∈ Sᶜ, (neighborsIn G S v).card ≤ 1) : False := by
  have hd := sparse_five_set_degree_bound S hS hout
  have hb := five_set_incidence_degree_budget hs hc h13 hsingle S hS
    (20 + Sᶜ.card) hd
  have hcard := Finset.card_add_card_compl S
  rw [hS] at hcard
  omega

end TaskH.Five

#print axioms TaskH.Five.neighborsIn_partition
#print axioms TaskH.Five.cross_neighbors_double_count
#print axioms TaskH.Five.sum_degrees_on_set
#print axioms TaskH.Five.internal_degree_sum_le_twenty
#print axioms TaskH.Five.sparse_five_set_degree_bound
#print axioms TaskH.Five.singleton_budget_on_set
#print axioms TaskH.Five.five_set_incidence_degree_budget
#print axioms TaskH.Five.no_sparse_five_vertex_set
