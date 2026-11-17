import Research.TaskH.Five.Definitions

/-!
Actual neighbor-color fibers. Criticality makes all five fibers nonempty;
their cardinalities imply at least 10-degree singleton colors. The chosen
neighbor of a singleton color is an actual neighbor, with proved uniqueness.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def neighborColorFiber (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (i : Fin 5) :
    Finset (G.neighborSet v) := by
  classical
  exact Finset.univ.filter (fun z => neighborColor v c z = i)

theorem mem_neighborColorFiber (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : Fin 5) (z : G.neighborSet v) :
    z ∈ neighborColorFiber v c i ↔ neighborColor v c z = i := by
  classical
  simp only [neighborColorFiber, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def singletonNeighborColors (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) : Finset (Fin 5) := by
  classical
  exact Finset.univ.filter (fun i => (neighborColorFiber v c i).card = 1)

theorem mem_singletonNeighborColors (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (i : Fin 5) :
    i ∈ singletonNeighborColors v c ↔ (neighborColorFiber v c i).card = 1 := by
  classical
  simp only [singletonNeighborColors, Finset.mem_filter, Finset.mem_univ, true_and]

theorem sum_neighborColorFiber_card (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) :
    (∑ i : Fin 5, (neighborColorFiber v c i).card) = Fintype.card (G.neighborSet v) := by
  classical
  simp only [neighborColorFiber, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem singletonNeighborColors_card_ge (hcrit : IsCriticalPlus 5 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) :
    10 - G.degree v ≤ (singletonNeighborColors v c).card := by
  classical
  let S := singletonNeighborColors v c
  have hpos : ∀ i : Fin 5, 0 < (neighborColorFiber v c i).card := by
    intro i
    obtain ⟨z, hz⟩ := critical_neighborColor_surjective hcrit v c i
    exact Finset.card_pos.mpr ⟨z, (mem_neighborColorFiber v c i z).mpr hz⟩
  have hstep : ∀ i ∈ (Finset.univ : Finset (Fin 5)),
      (if i ∈ S then 1 else 2 : ℕ) ≤ (neighborColorFiber v c i).card := by
    intro i _
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      exact ((mem_singletonNeighborColors v c i).mp hi).symm.le
    · rw [ite_eq_right hi]
      have hne : (neighborColorFiber v c i).card ≠ 1 := by
        intro he
        exact hi ((mem_singletonNeighborColors v c i).mpr he)
      have hp := hpos i
      omega
  have hsingle : (∑ i : Fin 5, if i ∈ S then 1 else 0 : ℕ) = S.card := by
    have hf : (Finset.univ.filter (fun i : Fin 5 => i ∈ S)) = S := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    calc
      (∑ i : Fin 5, if i ∈ S then 1 else 0 : ℕ) =
          (Finset.univ.filter (fun i : Fin 5 => i ∈ S)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = S.card := congrArg Finset.card hf
  have hpair : ∀ i : Fin 5,
      (if i ∈ S then 1 else 2 : ℕ) + (if i ∈ S then 1 else 0 : ℕ) = 2 := by
    intro i
    split_ifs <;> rfl
  have hten : (∑ i : Fin 5, if i ∈ S then 1 else 2 : ℕ) + S.card = 10 := by
    rw [← hsingle, ← Finset.sum_add_distrib]
    norm_num [hpair]
  have hle := Finset.sum_le_sum hstep
  have hsum := sum_neighborColorFiber_card v c
  rw [G.card_neighborSet_eq_degree] at hsum
  rw [hsum] at hle
  change 10 - G.degree v ≤ S.card
  omega

noncomputable def singletonNeighbor (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) : G.neighborSet v :=
  Classical.choose (Finset.card_eq_one.mp ((mem_singletonNeighborColors v c i.val).mp i.property))

theorem singletonNeighbor_fiber (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) :
    neighborColorFiber v c i.val = {singletonNeighbor v c i} :=
  Classical.choose_spec (Finset.card_eq_one.mp
    ((mem_singletonNeighborColors v c i.val).mp i.property))

theorem singletonNeighbor_color (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) : neighborColor v c (singletonNeighbor v c i) = i.val := by
  classical
  apply (mem_neighborColorFiber v c i.val _).mp
  rw [singletonNeighbor_fiber]
  exact Finset.mem_singleton_self _

theorem singletonNeighbor_eq_of_color (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) (z : G.neighborSet v)
    (hz : neighborColor v c z = i.val) : z = singletonNeighbor v c i := by
  classical
  have hm := (mem_neighborColorFiber v c i.val z).mpr hz
  rw [singletonNeighbor_fiber] at hm
  exact Finset.mem_singleton.mp hm

end TaskH.Five

#print axioms TaskH.Five.neighborColorFiber
#print axioms TaskH.Five.mem_neighborColorFiber
#print axioms TaskH.Five.singletonNeighborColors
#print axioms TaskH.Five.mem_singletonNeighborColors
#print axioms TaskH.Five.sum_neighborColorFiber_card
#print axioms TaskH.Five.singletonNeighborColors_card_ge
#print axioms TaskH.Five.singletonNeighbor
#print axioms TaskH.Five.singletonNeighbor_fiber
#print axioms TaskH.Five.singletonNeighbor_color
#print axioms TaskH.Five.singletonNeighbor_eq_of_color
