import Research.TaskH.Six.SixSplitLabelIntersection
import Research.TaskH.Six.SixNeighborPathRule

/-!
A genuine four-leaf star and the fixed deleted coloring force every multiple
outside attachment to the one remaining color. The application must supply
the six-color coverage from its actual degree-ten frame.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

theorem four_labels_choose_third_for_target (i j k : Fin 4) (hij : i ≠ j) :
    ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ (k = i ∨ k = j ∨ k = l) := by
  revert i j k
  decide +kernel

theorem four_leaf_multiple_attachment_forced_color
    {V : Type u} {G : SimpleGraph V}
    (hr : RainbowSixCycles G) (v a b : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (p : Fin 4 → V) (hp : Function.Injective p)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hvp : ∀ i, G.Adj v (p i)) (hap : ∀ i, G.Adj a (p i))
    (hcover : ∀ k : Fin 6,
      k = c ⟨a, hva.ne.symm⟩ ∨ k = c ⟨b, hvb.ne.symm⟩ ∨
        ∃ i : Fin 4, k = c ⟨p i, (hvp i).ne.symm⟩)
    (z : V) (hz : z ≠ v ∧ ¬ G.Adj v z)
    (hL : 2 ≤ (fourLeafLabels G p z).card) :
    c ⟨z, hz.1⟩ = c ⟨b, hvb.ne.symm⟩ := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hL
  have hzi := (mem_fourLeafLabels_iff p z i).mp hi
  have hzj := (mem_fourLeafLabels_iff p z j).mp hj
  let pc : Fin 4 → Fin 6 := fun k => c ⟨p k, (hvp k).ne.symm⟩
  let ac : Fin 6 := c ⟨a, hva.ne.symm⟩
  let zc : Fin 6 := c ⟨z, hz.1⟩
  have hza : z ≠ a := by intro he; exact hz.2 (by simpa only [he] using hva)
  have hzp : ∀ k, z ≠ p k := by
    intro k he
    exact hz.2 (by simpa only [he] using hvp k)
  have hzp_rev : ∀ k, p k ≠ z := fun k => (hzp k).symm
  have hpa : ∀ k, p k ≠ a := fun k => (hap k).ne.symm
  have hpath : ∀ l : Fin 4, l ≠ i → l ≠ j →
      Function.Injective (![pc i, zc, pc j, ac, pc l] : Fin 5 → Fin 6) := by
    intro l hli hlj
    let t : Fin 5 → V := ![p i, z, p j, a, p l]
    have hti : Function.Injective t := by
      intro x y he
      fin_cases x <;> fin_cases y <;> simp_all [t, hp.eq_iff]
    have htv : ∀ k, t k ≠ v := by
      intro k
      fin_cases k
      · exact (hvp i).ne.symm
      · exact hz.1
      · exact (hvp j).ne.symm
      · exact hva.ne.symm
      · exact (hvp l).ne.symm
    have htcolor := rainbow_five_path_colors_injective hr v c t hti htv
      (hvp i) hzi.symm hzj (hap j).symm (hap l) (hvp l).symm
    have he : (fun k => c ⟨t k, htv k⟩) =
        (![pc i, zc, pc j, ac, pc l] : Fin 5 → Fin 6) := by
      funext k
      fin_cases k <;> rfl
    rwa [he] at htcolor
  have hzc_ac : zc ≠ ac := by
    obtain ⟨l, hli, hlj, _⟩ := four_labels_choose_third_for_target i j 0 hij
    intro he
    have hh := (hpath l hli hlj) (show
      (![pc i, zc, pc j, ac, pc l] : Fin 5 → Fin 6) 1 =
        (![pc i, zc, pc j, ac, pc l] : Fin 5 → Fin 6) 3 from he)
    exact (by decide : (1 : Fin 5) ≠ 3) hh
  have hzc_pc : ∀ k : Fin 4, zc ≠ pc k := by
    intro k he
    obtain ⟨l, hli, hlj, hk⟩ := four_labels_choose_third_for_target i j k hij
    rcases hk with hki | hkj | hkl
    · have hh := (hpath l hli hlj) (show
        (![pc i, zc, pc j, ac, pc l] : Fin 5 → Fin 6) 1 =
          (![pc i, zc, pc j, ac, pc l] : Fin 5 → Fin 6) 0 from (show zc = pc i by simpa only [hki] using he))
      exact (by decide : (1 : Fin 5) ≠ 0) hh
    · have hh := (hpath l hli hlj) (show
        (![pc i, zc, pc j, ac, pc l] : Fin 5 → Fin 6) 1 =
          (![pc i, zc, pc j, ac, pc l] : Fin 5 → Fin 6) 2 from (show zc = pc j by simpa only [hkj] using he))
      exact (by decide : (1 : Fin 5) ≠ 2) hh
    · have hh := (hpath l hli hlj) (show
        (![pc i, zc, pc j, ac, pc l] : Fin 5 → Fin 6) 1 =
          (![pc i, zc, pc j, ac, pc l] : Fin 5 → Fin 6) 4 from (show zc = pc l by simpa only [hkl] using he))
      exact (by decide : (1 : Fin 5) ≠ 4) hh
  rcases hcover zc with ha | hb | ⟨k, hk⟩
  · exact False.elim (hzc_ac ha)
  · exact hb
  · exact False.elim (hzc_pc k hk)

end TaskH.Six

#print axioms TaskH.Six.four_labels_choose_third_for_target
#print axioms TaskH.Six.four_leaf_multiple_attachment_forced_color
