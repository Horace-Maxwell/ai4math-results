import Research.TaskH.FiniteBudget

/-! Actual graph boundary identities for the shortest-long-cycle step of BP45.
The internal and external capacities in these helpers are explicit intermediate
hypotheses. They still have to be proved for the actual shortest cycle; none is
an additional hypothesis in the frozen CaseSeven statement. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem boundary_degree_partition (S : Finset V) (x : V) :
    (G.neighborFinset x ∩ S).card + (G.neighborFinset x \ S).card = G.degree x := by
  simpa only [G.card_neighborFinset_eq_degree] using
    Finset.card_inter_add_card_sdiff (G.neighborFinset x) S

theorem boundary_double_count (S : Finset V) :
    (∑ x ∈ S, (G.neighborFinset x \ S).card) =
      ∑ y ∈ Finset.univ \ S, (G.neighborFinset y ∩ S).card := by
  classical
  have h := TaskH.FiniteBudget.relation_double_count S (Finset.univ \ S) G.Adj
  calc
    (∑ x ∈ S, (G.neighborFinset x \ S).card) =
        ∑ x ∈ S, ((Finset.univ \ S).filter (G.Adj x)).card := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      ext y
      simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact and_comm
    _ = ∑ y ∈ Finset.univ \ S, (S.filter (fun x => G.Adj x y)).card := h
    _ = ∑ y ∈ Finset.univ \ S, (G.neighborFinset y ∩ S).card := by
      apply Finset.sum_congr rfl
      intro y hy
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩

theorem boundary_capacity_budget (S : Finset V) (d p r : ℕ)
    (hd : ∀ x ∈ S, d ≤ G.degree x)
    (hi : ∀ x ∈ S, (G.neighborFinset x ∩ S).card ≤ p)
    (ho : ∀ y ∈ Finset.univ \ S, (G.neighborFinset y ∩ S).card ≤ r) :
    d * S.card ≤ p * S.card + r * (Fintype.card V - S.card) := by
  classical
  have hout : (∑ x ∈ S, (G.neighborFinset x \ S).card) ≤
      r * (Fintype.card V - S.card) := by
    rw [boundary_double_count S]
    calc
      (∑ y ∈ Finset.univ \ S, (G.neighborFinset y ∩ S).card) ≤
          ∑ _y ∈ Finset.univ \ S, r := Finset.sum_le_sum ho
      _ = r * (Fintype.card V - S.card) := by
        simp only [Finset.sum_const, smul_eq_mul, Finset.card_sdiff,
          Finset.inter_univ, Finset.card_univ]
        exact Nat.mul_comm _ _
  calc
    d * S.card = ∑ _x ∈ S, d := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_comm _ _
    _ ≤ ∑ x ∈ S, G.degree x := Finset.sum_le_sum hd
    _ = (∑ x ∈ S, (G.neighborFinset x ∩ S).card) +
        ∑ x ∈ S, (G.neighborFinset x \ S).card := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      exact (boundary_degree_partition S x).symm
    _ ≤ (∑ _x ∈ S, p) + r * (Fintype.card V - S.card) :=
      Nat.add_le_add (Finset.sum_le_sum hi) hout
    _ = p * S.card + r * (Fintype.card V - S.card) := by
      simp only [Finset.sum_const, smul_eq_mul]
      congr 1
      exact Nat.mul_comm _ _

theorem boundary_twenty_impossible (S : Finset V)
    (hn : Fintype.card V ≤ 49) (hS : S.card = 20)
    (hd : ∀ x ∈ S, 7 ≤ G.degree x)
    (hi : ∀ x ∈ S, (G.neighborFinset x ∩ S).card ≤ 4)
    (ho : ∀ y ∈ Finset.univ \ S, (G.neighborFinset y ∩ S).card ≤ 2) : False := by
  have h := boundary_capacity_budget S 7 4 2 hd hi ho
  omega

theorem boundary_twenty_two_impossible (S : Finset V)
    (hn : Fintype.card V ≤ 49) (hS : S.card = 22)
    (hd : ∀ x ∈ S, 7 ≤ G.degree x)
    (hi : ∀ x ∈ S, (G.neighborFinset x ∩ S).card ≤ 3)
    (ho : ∀ y ∈ Finset.univ \ S, (G.neighborFinset y ∩ S).card ≤ 2) : False := by
  have h := boundary_capacity_budget S 7 3 2 hd hi ho
  omega

theorem boundary_at_least_twenty_four_impossible (S : Finset V)
    (hn : Fintype.card V ≤ 49) (hS : 24 ≤ S.card)
    (hd : ∀ x ∈ S, 7 ≤ G.degree x)
    (hi : ∀ x ∈ S, (G.neighborFinset x ∩ S).card ≤ 2)
    (ho : ∀ y ∈ Finset.univ \ S, (G.neighborFinset y ∩ S).card ≤ 2) : False := by
  have h := boundary_capacity_budget S 7 2 2 hd hi ho
  have hcard : S.card ≤ Fintype.card V := Finset.card_le_univ S
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.boundary_degree_partition
#print axioms TaskH.Seven.BP.boundary_double_count
#print axioms TaskH.Seven.BP.boundary_capacity_budget
#print axioms TaskH.Seven.BP.boundary_twenty_impossible
#print axioms TaskH.Seven.BP.boundary_twenty_two_impossible
#print axioms TaskH.Seven.BP.boundary_at_least_twenty_four_impossible
