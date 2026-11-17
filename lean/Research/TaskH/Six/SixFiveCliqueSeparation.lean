import Research.TaskH.Six.SixFiveCliqueOutside
import Research.TaskH.Six.SixCliquePathPacking

/-!
Distinct actual five-clique attachment groups have no external edge and no
external common neighbor. Both contradictions use the actual four-clique
three-point-path theorem, with explicit injective root reindexings.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
theorem five_clique_outside_ne (q : Fin 5 → V) {x : V}
    (hx : x ∉ fiveCliqueSet q) (i : Fin 5) : q i ≠ x := by
  intro he
  apply hx
  rw [← he]
  exact (mem_fiveCliqueSet q _).mpr ⟨i, rfl⟩

def fiveSkipSecond : Fin 4 → Fin 5 := ![0, 2, 3, 4]

theorem fiveSkipSecond_injective : Function.Injective fiveSkipSecond := by decide +kernel

theorem fiveSkipSecond_ne_one (i : Fin 4) : fiveSkipSecond i ≠ 1 := by
  revert i
  decide +kernel

omit [DecidableRel G.Adj] in
theorem critical_five_clique_no_cross_edge
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G) (hn : 8 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (a b : Fin 5) (hab : a ≠ b) (x x' : V)
    (hx : x ∉ fiveCliqueSet q) (hx' : x' ∉ fiveCliqueSet q)
    (hax : G.Adj (q a) x) (hbx' : G.Adj (q b) x') : ¬ G.Adj x x' := by
  classical
  intro hxx'
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_five_pair_reindex a b hab
  let p : Fin 4 → V := fun i => q (ρ (fiveSkipSecond i))
  let t : Fin 3 → V := ![x, x', q b]
  have hp : Function.Injective p := hq.comp (ρ.injective.comp fiveSkipSecond_injective)
  have ht : Function.Injective t := by
    have hqx := five_clique_outside_ne q hx b
    have hqx' := five_clique_outside_ne q hx' b
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t, hxx'.ne]
  have hpt : ∀ i j, p i ≠ t j := by
    intro i j
    fin_cases j
    · exact five_clique_outside_ne q hx (ρ (fiveSkipSecond i))
    · exact five_clique_outside_ne q hx' (ρ (fiveSkipSecond i))
    · change q (ρ (fiveSkipSecond i)) ≠ q b
      intro he
      have hi : fiveSkipSecond i = 1 :=
        ρ.injective (hq (he.trans (congrArg q hρ1.symm)))
      exact fiveSkipSecond_ne_one i hi
  have hpclique : ∀ i j, i ≠ j → G.Adj (p i) (p j) := by
    intro i j hij
    exact hclique _ _ (ρ.injective.ne (fiveSkipSecond_injective.ne hij))
  have hleft : G.Adj (p 0) (t 0) := by
    change G.Adj (q (ρ 0)) x
    rw [hρ0]
    exact hax
  have hright : G.Adj (t 2) (p 1) := by
    change G.Adj (q b) (q (ρ 2))
    rw [← hρ1]
    exact hclique _ _ (ρ.injective.ne (by decide : (1 : Fin 5) ≠ 2))
  exact critical_no_four_clique_external_three_path hcrit hr hn p t hp ht hpt hpclique
    hleft hxx' hbx'.symm hright

omit [DecidableRel G.Adj] in
theorem critical_five_clique_no_cross_common_neighbor
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G) (hn : 8 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (a b : Fin 5) (hab : a ≠ b) (x x' z : V)
    (hx : x ∉ fiveCliqueSet q) (hx' : x' ∉ fiveCliqueSet q)
    (hz : z ∉ fiveCliqueSet q) (hxx' : x ≠ x')
    (hax : G.Adj (q a) x) (hbx' : G.Adj (q b) x')
    (hxz : G.Adj x z) (hx'z : G.Adj x' z) : False := by
  classical
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_five_pair_reindex a b hab
  let p : Fin 4 → V := fun i => q (ρ i.castSucc)
  let t : Fin 3 → V := ![x, z, x']
  have hcast : Function.Injective (fun i : Fin 4 => i.castSucc) := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin 5 => x.val) hij)
  have hp : Function.Injective p := hq.comp (ρ.injective.comp hcast)
  have ht : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t, hxz.ne, hx'z.ne]
  have hpt : ∀ i j, p i ≠ t j := by
    intro i j
    fin_cases j
    · exact five_clique_outside_ne q hx (ρ i.castSucc)
    · exact five_clique_outside_ne q hz (ρ i.castSucc)
    · exact five_clique_outside_ne q hx' (ρ i.castSucc)
  have hpclique : ∀ i j, i ≠ j → G.Adj (p i) (p j) := by
    intro i j hij
    exact hclique _ _ (ρ.injective.ne (hcast.ne hij))
  have hleft : G.Adj (p 0) (t 0) := by
    change G.Adj (q (ρ 0)) x
    rw [hρ0]
    exact hax
  have hright : G.Adj (t 2) (p 1) := by
    change G.Adj x' (q (ρ 1))
    rw [hρ1]
    exact hbx'.symm
  exact critical_no_four_clique_external_three_path hcrit hr hn p t hp ht hpt hpclique
    hleft hxz hx'z.symm hright

end TaskH.Six

#print axioms TaskH.Six.five_clique_outside_ne
#print axioms TaskH.Six.fiveSkipSecond
#print axioms TaskH.Six.fiveSkipSecond_injective
#print axioms TaskH.Six.fiveSkipSecond_ne_one
#print axioms TaskH.Six.critical_five_clique_no_cross_edge
#print axioms TaskH.Six.critical_five_clique_no_cross_common_neighbor
