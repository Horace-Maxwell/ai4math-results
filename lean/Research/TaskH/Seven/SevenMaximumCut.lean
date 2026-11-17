import Mathlib

/-! A finite maximum cut constructed from all Boolean vertex colorings.
The score counts each unordered crossing edge twice. This avoids an
orientation choice and gives the same single-vertex maximality inequality.
No criticality, order, or supplied cut hypothesis occurs in the conclusion.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Finset
open scoped Classical
open scoped BigOperators

variable {V : Type u}

noncomputable def crossingWeight (G : SimpleGraph V) (c : V → Bool) (a b : V) : ℕ := by
  classical
  exact if G.Adj a b ∧ c a ≠ c b then 1 else 0

noncomputable def sameSideWeight (G : SimpleGraph V) (c : V → Bool) (a b : V) : ℕ := by
  classical
  exact if G.Adj a b ∧ c a = c b then 1 else 0

noncomputable def flipColor (c : V → Bool) (x : V) : V → Bool := by
  classical
  exact Function.update c x (!(c x))

noncomputable def cutScore [Fintype V] (G : SimpleGraph V) (c : V → Bool) : ℕ :=
  ∑ a : V, ∑ b : V, crossingWeight G c a b

noncomputable def crossDegree [Fintype V] (G : SimpleGraph V) (c : V → Bool) (x : V) : ℕ :=
  ∑ y : V, crossingWeight G c x y

noncomputable def sameSideDegree [Fintype V] (G : SimpleGraph V) (c : V → Bool) (x : V) : ℕ :=
  ∑ y : V, sameSideWeight G c x y

theorem crossingWeight_symm (G : SimpleGraph V) (c : V → Bool) (a b : V) :
    crossingWeight G c a b = crossingWeight G c b a := by
  classical
  simp only [crossingWeight, G.adj_comm, ne_comm]

theorem sameSideWeight_symm (G : SimpleGraph V) (c : V → Bool) (a b : V) :
    sameSideWeight G c a b = sameSideWeight G c b a := by
  classical
  simp only [sameSideWeight, G.adj_comm, eq_comm]

theorem flip_pair_balance (G : SimpleGraph V) (c : V → Bool) (x a b : V) :
    crossingWeight G (flipColor c x) a b +
        (if a = x then crossingWeight G c a b else 0) +
        (if b = x then crossingWeight G c a b else 0) =
      crossingWeight G c a b +
        (if a = x then sameSideWeight G c a b else 0) +
        (if b = x then sameSideWeight G c a b else 0) := by
  classical
  by_cases ha : a = x
  · subst a
    by_cases hb : b = x
    · subst b
      simp [crossingWeight, sameSideWeight, flipColor]
    · cases hcx : c x <;> cases hcb : c b <;> by_cases hab : G.Adj x b <;>
        simp [crossingWeight, sameSideWeight, flipColor, Function.update,
          hb, hcx, hcb, hab]
  · by_cases hb : b = x
    · subst b
      cases hca : c a <;> cases hcx : c x <;> by_cases hab : G.Adj a x <;>
        simp [crossingWeight, sameSideWeight, flipColor, Function.update,
          ha, hca, hcx, hab]
    · simp [crossingWeight, flipColor, Function.update, ha, hb]

theorem flip_score_balance [Fintype V] (G : SimpleGraph V) (c : V → Bool) (x : V) :
    cutScore G (flipColor c x) + 2 * crossDegree G c x =
      cutScore G c + 2 * sameSideDegree G c x := by
  classical
  have hs := congrArg (fun f : V → V → ℕ => ∑ a : V, ∑ b : V, f a b)
    (funext fun a => funext fun b => flip_pair_balance G c x a b)
  have hc : (∑ a : V, crossingWeight G c a x) = crossDegree G c x := by
    unfold crossDegree
    exact Finset.sum_congr rfl (fun a _ => crossingWeight_symm G c a x)
  have hm : (∑ a : V, sameSideWeight G c a x) = sameSideDegree G c x := by
    unfold sameSideDegree
    exact Finset.sum_congr rfl (fun a _ => sameSideWeight_symm G c a x)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hs
  change cutScore G (flipColor c x) + crossDegree G c x +
      (∑ a : V, crossingWeight G c a x) =
    cutScore G c + sameSideDegree G c x +
      (∑ a : V, sameSideWeight G c a x) at hs
  rw [hc, hm] at hs
  omega

theorem cross_same_partition [Fintype V] (G : SimpleGraph V) (c : V → Bool) (x : V) :
    crossDegree G c x + sameSideDegree G c x = G.degree x := by
  classical
  have hp (y : V) : crossingWeight G c x y + sameSideWeight G c x y =
      (if G.Adj x y then 1 else 0) := by
    by_cases h : G.Adj x y <;> by_cases hc : c x = c y <;>
      simp [crossingWeight, sameSideWeight, h, hc]
  calc
    crossDegree G c x + sameSideDegree G c x =
        ∑ y : V, (if G.Adj x y then 1 else 0) := by
      rw [crossDegree, sameSideDegree, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun y _ => hp y)
    _ = (G.neighborFinset x).card := by
      rw [G.neighborFinset_eq_filter]
      simp
    _ = G.degree x := G.card_neighborFinset_eq_degree x

def cutGraph (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ c a ≠ c b
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨by
    intro a h
    exact h.2 rfl⟩

theorem cutGraph_le (G : SimpleGraph V) (c : V → Bool) : cutGraph G c ≤ G := by
  intro a b h
  exact h.1

theorem cutGraph_isBipartite (G : SimpleGraph V) (c : V → Bool) :
    (cutGraph G c).IsBipartite := by
  have C : (cutGraph G c).Coloring Bool := SimpleGraph.Coloring.mk c (by
    intro a b h
    exact h.2)
  simpa using C.colorable

theorem cutGraph_degree [Fintype V] (G : SimpleGraph V) (c : V → Bool) (x : V) :
    (cutGraph G c).degree x = crossDegree G c x := by
  classical
  rw [← (cutGraph G c).card_neighborFinset_eq_degree x]
  simp only [crossDegree, crossingWeight, Finset.sum_boole]
  apply congrArg Finset.card
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rfl

theorem exists_bipartite_subgraph_half_degree [Fintype V] (G : SimpleGraph V) :
    ∃ B : SimpleGraph V, B ≤ G ∧ B.IsBipartite ∧
      ∀ x : V, G.degree x ≤ 2 * B.degree x := by
  classical
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image (Finset.univ : Finset (V → Bool))
    (cutScore G) Finset.univ_nonempty
  refine ⟨cutGraph G c, cutGraph_le G c, cutGraph_isBipartite G c, ?_⟩
  intro x
  have hm := hc (flipColor c x) (Finset.mem_univ _)
  have hb := flip_score_balance G c x
  have hp := cross_same_partition G c x
  rw [cutGraph_degree G c x]
  omega

theorem exists_bipartite_subgraph_min_degree_seven [Fintype V] (G : SimpleGraph V)
    (hd : ∀ x : V, 13 ≤ G.degree x) :
    ∃ B : SimpleGraph V, B ≤ G ∧ B.IsBipartite ∧ ∀ x : V, 7 ≤ B.degree x := by
  obtain ⟨B, hle, hb, hdeg⟩ := exists_bipartite_subgraph_half_degree G
  refine ⟨B, hle, hb, ?_⟩
  intro x
  have h1 := hd x
  have h2 := hdeg x
  omega

end TaskH.Seven

#print axioms TaskH.Seven.crossingWeight
#print axioms TaskH.Seven.sameSideWeight
#print axioms TaskH.Seven.flipColor
#print axioms TaskH.Seven.cutScore
#print axioms TaskH.Seven.crossDegree
#print axioms TaskH.Seven.sameSideDegree
#print axioms TaskH.Seven.crossingWeight_symm
#print axioms TaskH.Seven.sameSideWeight_symm
#print axioms TaskH.Seven.flip_pair_balance
#print axioms TaskH.Seven.flip_score_balance
#print axioms TaskH.Seven.cross_same_partition
#print axioms TaskH.Seven.cutGraph
#print axioms TaskH.Seven.cutGraph_le
#print axioms TaskH.Seven.cutGraph_isBipartite
#print axioms TaskH.Seven.cutGraph_degree
#print axioms TaskH.Seven.exists_bipartite_subgraph_half_degree
#print axioms TaskH.Seven.exists_bipartite_subgraph_min_degree_seven
