import Research.TaskH.Seven.SevenK6CliqueOutside
import Research.TaskH.Seven.SevenK5Path

/-!
Distinct actual six-clique attachment groups have no external edge and no
external common neighbor. Both contradictions use the actual five-clique
three-point-path theorem, with explicit injective root reindexings.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
theorem six_clique_outside_ne (q : Fin 6 → V) {x : V}
    (hx : x ∉ sixCliqueSet q) (i : Fin 6) : q i ≠ x := by
  intro he
  apply hx
  rw [← he]
  exact (mem_sixCliqueSet q _).mpr ⟨i, rfl⟩

def sixSkipSecond : Fin 5 → Fin 6 := ![0, 2, 3, 4, 5]

theorem sixSkipSecond_injective : Function.Injective sixSkipSecond := by decide +kernel

theorem sixSkipSecond_ne_one (i : Fin 5) : sixSkipSecond i ≠ 1 := by
  revert i
  decide +kernel

omit [DecidableRel G.Adj] in
theorem critical_six_clique_no_cross_edge
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G) (hn : 9 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (a b : Fin 6) (hab : a ≠ b) (x x' : V)
    (hx : x ∉ sixCliqueSet q) (hx' : x' ∉ sixCliqueSet q)
    (hax : G.Adj (q a) x) (hbx' : G.Adj (q b) x') : ¬ G.Adj x x' := by
  classical
  intro hxx'
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_six_pair_reindex a b hab
  let p : Fin 5 → V := fun i => q (ρ (sixSkipSecond i))
  let t : Fin 3 → V := ![x, x', q b]
  have hp : Function.Injective p := hq.comp (ρ.injective.comp sixSkipSecond_injective)
  have ht : Function.Injective t := by
    have hqx := six_clique_outside_ne q hx b
    have hqx' := six_clique_outside_ne q hx' b
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t, hxx'.ne]
  have hpt : ∀ i j, p i ≠ t j := by
    intro i j
    fin_cases j
    · exact six_clique_outside_ne q hx (ρ (sixSkipSecond i))
    · exact six_clique_outside_ne q hx' (ρ (sixSkipSecond i))
    · change q (ρ (sixSkipSecond i)) ≠ q b
      intro he
      have hi : sixSkipSecond i = 1 :=
        ρ.injective (hq (he.trans (congrArg q hρ1.symm)))
      exact sixSkipSecond_ne_one i hi
  have hpclique : ∀ i j, i ≠ j → G.Adj (p i) (p j) := by
    intro i j hij
    exact hclique _ _ (ρ.injective.ne (sixSkipSecond_injective.ne hij))
  have hleft : G.Adj (p 0) (t 0) := by
    change G.Adj (q (ρ 0)) x
    rw [hρ0]
    exact hax
  have hright : G.Adj (t 2) (p 1) := by
    change G.Adj (q b) (q (ρ 2))
    rw [← hρ1]
    exact hclique _ _ (ρ.injective.ne (by decide : (1 : Fin 6) ≠ 2))
  exact critical_no_five_clique_external_three_path hcrit hr hn p t hp ht hpt hpclique
    hleft hxx' hbx'.symm hright

omit [DecidableRel G.Adj] in
theorem critical_six_clique_no_cross_common_neighbor
    (hcrit : IsCriticalPlus 7 G) (hr : RainbowSevenCycles G) (hn : 9 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (a b : Fin 6) (hab : a ≠ b) (x x' z : V)
    (hx : x ∉ sixCliqueSet q) (hx' : x' ∉ sixCliqueSet q)
    (hz : z ∉ sixCliqueSet q) (hxx' : x ≠ x')
    (hax : G.Adj (q a) x) (hbx' : G.Adj (q b) x')
    (hxz : G.Adj x z) (hx'z : G.Adj x' z) : False := by
  classical
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_six_pair_reindex a b hab
  let p : Fin 5 → V := fun i => q (ρ i.castSucc)
  let t : Fin 3 → V := ![x, z, x']
  have hcast : Function.Injective (fun i : Fin 5 => i.castSucc) := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin 6 => x.val) hij)
  have hp : Function.Injective p := hq.comp (ρ.injective.comp hcast)
  have ht : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t, hxz.ne, hx'z.ne]
  have hpt : ∀ i j, p i ≠ t j := by
    intro i j
    fin_cases j
    · exact six_clique_outside_ne q hx (ρ i.castSucc)
    · exact six_clique_outside_ne q hz (ρ i.castSucc)
    · exact six_clique_outside_ne q hx' (ρ i.castSucc)
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
  exact critical_no_five_clique_external_three_path hcrit hr hn p t hp ht hpt hpclique
    hleft hxz hx'z.symm hright

end TaskH.Seven

#print axioms TaskH.Seven.six_clique_outside_ne
#print axioms TaskH.Seven.sixSkipSecond
#print axioms TaskH.Seven.sixSkipSecond_injective
#print axioms TaskH.Seven.sixSkipSecond_ne_one
#print axioms TaskH.Seven.critical_six_clique_no_cross_edge
#print axioms TaskH.Seven.critical_six_clique_no_cross_common_neighbor
