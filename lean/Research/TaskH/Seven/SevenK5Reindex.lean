import Research.TaskH.Seven.SevenK5Path
import Research.TaskH.Seven.SevenK4LongPath

/-! Reindex the actual clique to the two distinct attachment roots.
The four-point outside-path case uses an actual four-vertex clique subset;
the deleted coloring need not retain an unused fifth clique point. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} {G : SimpleGraph V}

theorem exists_five_index_order_zero_one (a b : Fin 5) (hab : a ≠ b) :
    ∃ π : Equiv.Perm (Fin 5), π a = 0 ∧ π b = 1 := by
  classical
  let τ : Equiv.Perm (Fin 5) := Equiv.swap a 0
  have hτa : τ a = 0 := by simp [τ]
  have hτb : τ b ≠ 0 := by
    intro he
    exact hab (τ.injective (hτa.trans he.symm))
  let π : Equiv.Perm (Fin 5) := τ.trans (Equiv.swap (τ b) 1)
  refine ⟨π, ?_, ?_⟩
  · change Equiv.swap (τ b) 1 (τ a) = 0
    rw [hτa]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hτb) (by decide)
  · change Equiv.swap (τ b) 1 (τ b) = 1
    exact Equiv.swap_apply_left _ _

theorem critical_no_five_clique_external_three_path_at [Fintype V]
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V)
    (q : Fin 5 → V) (t : Fin 3 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (a b : Fin 5) (hab : a ≠ b)
    (hleft : G.Adj (q a) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (hright : G.Adj (t 2) (q b)) : False := by
  obtain ⟨π, hπa, hπb⟩ := exists_five_index_order_zero_one a b hab
  have hπ0 : π.symm 0 = a := by rw [← hπa, π.symm_apply_apply]
  have hπ1 : π.symm 1 = b := by rw [← hπb, π.symm_apply_apply]
  let q' : Fin 5 → V := fun i => q (π.symm i)
  have hq' : Function.Injective q' := hq.comp π.symm.injective
  have hq't : ∀ i j, q' i ≠ t j := fun i j => hqt (π.symm i) j
  have hclique' : ∀ i j, i ≠ j → G.Adj (q' i) (q' j) := by
    intro i j hij
    exact hclique _ _ (π.symm.injective.ne hij)
  have hleft' : G.Adj (q' 0) (t 0) := by
    change G.Adj (q (π.symm 0)) (t 0)
    rw [hπ0]
    exact hleft
  have hright' : G.Adj (t 2) (q' 1) := by
    change G.Adj (t 2) (q (π.symm 1))
    rw [hπ1]
    exact hright
  exact critical_no_five_clique_external_three_path hcrit hr hn q' t
    hq' ht hq't hclique' hleft' h01 h12 hright'

theorem critical_no_five_clique_external_four_path_at [Fintype V]
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V)
    (q : Fin 5 → V) (t : Fin 4 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (a b : Fin 5) (hab : a ≠ b)
    (hleft : G.Adj (q a) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (h23 : G.Adj (t 2) (t 3))
    (hright : G.Adj (t 3) (q b)) : False := by
  obtain ⟨π, hπa, hπb⟩ := exists_five_index_order_zero_one a b hab
  have hπ0 : π.symm 0 = a := by rw [← hπa, π.symm_apply_apply]
  have hπ1 : π.symm 1 = b := by rw [← hπb, π.symm_apply_apply]
  let g : Fin 4 → V := fun i => q (π.symm i.castSucc)
  have hg : Function.Injective g := hq.comp (π.symm.injective.comp (Fin.castSucc_injective 4))
  have hgt : ∀ i j, g i ≠ t j := fun i j => hqt (π.symm i.castSucc) j
  have hclique' : ∀ i j, i ≠ j → G.Adj (g i) (g j) := by
    intro i j hij
    exact hclique _ _ (π.symm.injective.ne ((Fin.castSucc_injective 4).ne hij))
  have hleft' : G.Adj (g 0) (t 0) := by
    change G.Adj (q (π.symm 0)) (t 0)
    rw [hπ0]
    exact hleft
  have hright' : G.Adj (t 3) (g 1) := by
    change G.Adj (t 3) (q (π.symm 1))
    rw [hπ1]
    exact hright
  exact critical_no_four_clique_external_four_path hcrit hr hn g t hg ht hgt
    hclique' hleft' h01 h12 h23 hright'

end TaskH.Seven

#print axioms TaskH.Seven.exists_five_index_order_zero_one
#print axioms TaskH.Seven.critical_no_five_clique_external_three_path_at
#print axioms TaskH.Seven.critical_no_five_clique_external_four_path_at
