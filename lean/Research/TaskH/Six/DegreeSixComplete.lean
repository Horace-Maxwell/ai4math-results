import Research.TaskH.Six.SingletonClique
import Research.TaskH.Six.CliqueCompletion

/-!
Degree six forces all six neighbor colors to be singletons. The actual
singleton-clique theorem therefore yields a seven-clique, and criticality
makes it span the graph. No cycle-budget assumption is needed in this branch
once S and R have been derived from the original equality hypotheses.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem degreeSix_singleton_colors_univ (hcrit : IsCriticalPlus 6 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) (hv : G.degree v = 6) :
    singletonNeighborColors v c = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  have hle := singletonNeighborColors_card_ge hcrit v c
  rw [hv] at hle
  have hupper := Finset.card_le_univ (singletonNeighborColors v c)
  norm_num only [Fintype.card_fin] at hupper ⊢
  omega

theorem degreeSix_neighbors_adj (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) (hv : G.degree v = 6)
    {a b : V} (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) : G.Adj a b := by
  classical
  have hS := degreeSix_singleton_colors_univ hcrit v c hv
  have hcard : 3 ≤ (singletonNeighborColors v c).card := by rw [hS]; decide
  let na : G.neighborSet v := ⟨a, ha⟩
  let nb : G.neighborSet v := ⟨b, hb⟩
  let i : ↥(singletonNeighborColors v c) :=
    ⟨neighborColor v c na, by rw [hS]; exact Finset.mem_univ _⟩
  let j : ↥(singletonNeighborColors v c) :=
    ⟨neighborColor v c nb, by rw [hS]; exact Finset.mem_univ _⟩
  have hia : na = singletonNeighbor v c i := singletonNeighbor_eq_of_color v c i na rfl
  have hjb : nb = singletonNeighbor v c j := singletonNeighbor_eq_of_color v c j nb rfl
  have hij : i ≠ j := by
    intro he
    have hn : na = nb := hia.trans ((congrArg (singletonNeighbor v c) he).trans hjb.symm)
    exact hab (congrArg Subtype.val hn)
  have hAdj := singleton_neighbors_adj hcrit hs hr v c hcard i j hij
  change G.Adj na.val nb.val
  rw [hia, hjb]
  exact hAdj

theorem degreeSix_closed_neighborhood_clique (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) (hv : G.degree v = 6) :
    G.IsClique (insert v (G.neighborFinset v) : Finset V) := by
  classical
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
  rcases ha with hav | ha
  · rcases hb with hbv | hb
    · exact (hab (hav.trans hbv.symm)).elim
    · rw [hav]
      exact (G.mem_neighborFinset v b).mp hb
  · rcases hb with hbv | hb
    · rw [hbv]
      exact ((G.mem_neighborFinset v a).mp ha).symm
    · exact degreeSix_neighbors_adj hcrit hs hr v c hv
        ((G.mem_neighborFinset v a).mp ha) ((G.mem_neighborFinset v b).mp hb) hab

theorem degreeSix_isCompleteOfOrder (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (v : V) (hv : G.degree v = 6) : IsCompleteOfOrder G 7 := by
  classical
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  apply critical_seven_clique_complete hcrit (insert v (G.neighborFinset v))
    (degreeSix_closed_neighborhood_clique hcrit hs hr v c hv)
  calc
    (insert v (G.neighborFinset v)).card = (G.neighborFinset v).card + 1 :=
      Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v)
    _ = 7 := by rw [G.card_neighborFinset_eq_degree, hv]

end TaskH.Six

#print axioms TaskH.Six.degreeSix_singleton_colors_univ
#print axioms TaskH.Six.degreeSix_neighbors_adj
#print axioms TaskH.Six.degreeSix_closed_neighborhood_clique
#print axioms TaskH.Six.degreeSix_isCompleteOfOrder
