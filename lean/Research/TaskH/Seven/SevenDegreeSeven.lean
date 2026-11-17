import Research.TaskH.Seven.SingletonClique
import Research.TaskH.Seven.SevenCliqueCompletion

/-!
Actual degree seven makes every neighbor color a singleton. The genuine
singleton-clique transport yields the closed-neighborhood eight-clique, and
full criticality forces it to be the whole graph. S and R are internal
conclusions to be supplied by the original equality prefix, not main assumptions.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem degreeSeven_singleton_colors_univ (hcrit : IsCriticalPlus 7 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 7) :
    singletonNeighborColors v c = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  have hle := singletonNeighborColors_card_ge hcrit v c
  rw [hv] at hle
  have hupper := Finset.card_le_univ (singletonNeighborColors v c)
  norm_num only [Fintype.card_fin] at hupper ⊢
  omega

theorem degreeSeven_neighbors_adj (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 7)
    {a b : V} (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) : G.Adj a b := by
  classical
  have hS := degreeSeven_singleton_colors_univ hcrit v c hv
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

theorem degreeSeven_closed_neighborhood_clique (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 7) :
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
    · exact degreeSeven_neighbors_adj hcrit hs hr v c hv
        ((G.mem_neighborFinset v a).mp ha) ((G.mem_neighborFinset v b).mp hb) hab

theorem degreeSeven_isCompleteOfOrder (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (v : V) (hv : G.degree v = 7) : IsCompleteOfOrder G 8 := by
  classical
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  apply critical_eight_clique_complete hcrit (insert v (G.neighborFinset v))
    (degreeSeven_closed_neighborhood_clique hcrit hs hr v c hv)
  calc
    (insert v (G.neighborFinset v)).card = (G.neighborFinset v).card + 1 :=
      Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v)
    _ = 8 := by rw [G.card_neighborFinset_eq_degree, hv]

end TaskH.Seven

#print axioms TaskH.Seven.degreeSeven_singleton_colors_univ
#print axioms TaskH.Seven.degreeSeven_neighbors_adj
#print axioms TaskH.Seven.degreeSeven_closed_neighborhood_clique
#print axioms TaskH.Seven.degreeSeven_isCompleteOfOrder
