import Research.TaskH.Seven.SevenK5Reindex

/-!
Distinctly rooted outside vertices cannot share an outside neighbor. This
is the actual-graph input to the later open-neighborhood packing; the roots
are real clique vertices and all three outside vertices are retained.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem five_clique_distinct_roots_common_neighbor_unique
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (x y z : V) (hx : ∀ i, q i ≠ x) (hy : ∀ i, q i ≠ y)
    (hz : ∀ i, q i ≠ z)
    (a b : Fin 5) (hab : a ≠ b)
    (hax : G.Adj (q a) x) (hby : G.Adj (q b) y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) : x = y := by
  classical
  by_contra hxy
  let t : Fin 3 → V := ![x, z, y]
  have hzx : z ≠ x := hxz.ne.symm
  have hzy : z ≠ y := hyz.ne.symm
  have hyx : y ≠ x := Ne.symm hxy
  have ht : Function.Injective t := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [t]
  have hqt : ∀ i j, q i ≠ t j := by
    intro i j
    fin_cases j
    · exact hx i
    · exact hz i
    · exact hy i
  exact critical_no_five_clique_external_three_path_at hcrit hr hn q t hq ht hqt
    hclique a b hab hax hxz hyz.symm hby.symm

end TaskH.Seven

#print axioms TaskH.Seven.five_clique_distinct_roots_common_neighbor_unique
