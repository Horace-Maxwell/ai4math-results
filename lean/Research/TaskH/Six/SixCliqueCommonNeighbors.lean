import Research.TaskH.Six.SixCliquePathPacking
import Research.TaskH.Six.SixOpenNeighborhoodPacking

/-! Actual common-neighbor restrictions for external four-clique attachments. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

theorem four_permutation_prescribed_pair (a b : Fin 4) (hne : a ≠ b) :
    ∃ e : Equiv.Perm (Fin 4), e 0 = a ∧ e 1 = b := by
  revert a b
  decide +kernel

theorem critical_no_four_clique_external_three_path_at [Fintype V]
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn : 8 ≤ Fintype.card V)
    (q : Fin 4 → V) (t : Fin 3 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (a b : Fin 4) (hab : a ≠ b)
    (hleft : G.Adj (q a) (t 0)) (h01 : G.Adj (t 0) (t 1))
    (h12 : G.Adj (t 1) (t 2)) (hright : G.Adj (t 2) (q b)) : False := by
  obtain ⟨e, he0, he1⟩ := four_permutation_prescribed_pair a b hab
  let q' : Fin 4 → V := q ∘ e
  have hq' : Function.Injective q' := hq.comp e.injective
  have hqt' : ∀ i j, q' i ≠ t j := fun i j => hqt (e i) j
  have hclique' : ∀ i j, i ≠ j → G.Adj (q' i) (q' j) := by
    intro i j hij
    exact hclique (e i) (e j) (fun he => hij (e.injective he))
  have hl : G.Adj (q' 0) (t 0) := by simpa [q', he0] using hleft
  have hh : G.Adj (t 2) (q' 1) := by simpa [q', he1] using hright
  exact critical_no_four_clique_external_three_path hcrit hr hn q' t hq' ht hqt'
    hclique' hl h01 h12 hh

theorem four_clique_common_neighbor_labels_equal [Fintype V]
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn : 8 ≤ Fintype.card V) (q : Fin 4 → V)
    (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (x y z : V) (hxy : x ≠ y)
    (hxq : ∀ i, q i ≠ x) (hyq : ∀ i, q i ≠ y) (hzq : ∀ i, q i ≠ z)
    (hxz : G.Adj x z) (hyz : G.Adj y z)
    (a b : Fin 4) (hax : G.Adj (q a) x) (hby : G.Adj (q b) y) : a = b := by
  by_contra hab
  let t : Fin 3 → V := ![x, z, y]
  have hti : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t, hxz.ne, hyz.ne]
  have hqt : ∀ i j, q i ≠ t j := by
    intro i j
    fin_cases j <;> simp [t, hxq, hyq, hzq]
  exact critical_no_four_clique_external_three_path_at hcrit hr hn q t hq hti hqt
    hclique a b hab hax hxz hyz.symm hby.symm

theorem four_clique_selected_attachment_common_neighbor_unique [Fintype V]
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn : 8 ≤ Fintype.card V) (q : Fin 4 → V)
    (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (T : Finset V) (hout : ∀ x ∈ T, ∀ i, q i ≠ x)
    (hlabels : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      ∃ a b : Fin 4, a ≠ b ∧ G.Adj (q a) x ∧ G.Adj (q b) y)
    (z : V) (hzq : ∀ i, q i ≠ z)
    (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ T)
    (hxz : G.Adj x z) (hyz : G.Adj y z) : x = y := by
  by_contra hxy
  obtain ⟨a, b, hab, hax, hby⟩ := hlabels x hx y hy hxy
  exact hab (four_clique_common_neighbor_labels_equal hcrit hr hn q hq hclique
    x y z hxy (hout x hx) (hout y hy) hzq hxz hyz a b hax hby)

end TaskH.Six

#print axioms TaskH.Six.four_permutation_prescribed_pair
#print axioms TaskH.Six.critical_no_four_clique_external_three_path_at
#print axioms TaskH.Six.four_clique_common_neighbor_labels_equal
#print axioms TaskH.Six.four_clique_selected_attachment_common_neighbor_unique
