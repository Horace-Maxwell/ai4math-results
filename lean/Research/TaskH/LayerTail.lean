import Research.TaskH.LayerColoring
import Research.TaskH.FourColorPerms

/-!
Exact tail layers for every assigned shifted-monochromatic edge.
The old root-edge case derives its distance from the genuine four-color
successor relation; no distance premise is added to the coloring data.
-/

universe u

namespace TaskH.LayerTail

open SimpleGraph LayerColoring

variable {V : Type u} {G : SimpleGraph V} {v : V}

/-- Appending an actual successor edge advances the endpoint color once. -/
theorem chain_endColor {α : Type*} (c : V → α) (σ : Equiv.Perm α)
    {x y : V} {n : ℕ} (h : LayerSets.Chain (ColorStep G c σ) x n y) :
    c y = (σ ^ n) (c x) := by
  induction h with
  | nil => rfl
  | @tail n a b _ hab ih =>
    calc
      c b = σ (c a) := hab.2
      _ = σ ((σ ^ n) (c x)) := congrArg σ ih
      _ = (σ ^ (n + 1)) (c x) := by
        rw [pow_succ']
        rfl

theorem chain_end_eq_of_zero {R' : V → V → Prop} {x y : V}
    (h : LayerSets.Chain R' x 0 y) : y = x := by
  cases h
  rfl

/-- Returning from label 3 to label 3 takes a multiple of four successor steps. -/
theorem target_chain_length_dvd (c : (G.induce {x | x ≠ v}).Coloring (Fin 4))
    (π : Equiv.Perm (Fin 4)) {z : V} {n : ℕ} (hz : z ∈ Z c π)
    (hchain : LayerSets.Chain (R c π) v n z) : 4 ∣ n := by
  have hc := chain_endColor (baseColor c π) (finRotate 4) hchain
  rw [baseColor_root] at hc
  have hfix : ((finRotate 4) ^ n) (3 : Fin 4) = 3 := hc.symm.trans hz.2
  apply (fourColorCycle_pow_fixed_iff (0 : Fin 3) (3 : Fin 4) n).mp
  change ((finRotate 4) ^ n) (3 : Fin 4) = 3
  exact hfix

/-- No original monochromatic root neighbor is reached in fewer than four steps. -/
theorem target_not_mem_S_four (c : (G.induce {x | x ≠ v}).Coloring (Fin 4))
    (π : Equiv.Perm (Fin 4)) {z : V} (hz : z ∈ Z c π) :
    z ∉ LayerSets.S (R c π) v 4 := by
  rintro ⟨n, hn, hchain⟩
  have hdiv := target_chain_length_dvd c π hz hchain
  have hnzero : n = 0 := by
    obtain ⟨m, hm⟩ := hdiv
    omega
  subst n
  exact hz.1.ne (chain_end_eq_of_zero hchain).symm

/-- A surviving old monochromatic root edge occurs only at layer five. -/
theorem old_mono_tail (c : (G.induce {x | x ≠ v}).Coloring (Fin 4))
    (π : Equiv.Perm (Fin 4)) {i : ℕ} (hi : i ≤ 5) {z : V}
    (hz : z ∈ Z c π) (hzt : z ∉ Ti c π i) :
    i = 5 ∧ LayerSets.Chain (R c π) v (i - 1) z ∧
      z ∈ Ti c π (i - 1) \ Ti c π i := by
  classical
  have hzs : z ∈ LayerSets.S (R c π) v i := by
    by_contra hzs
    exact hzt ((LayerSets.target_mem_T_iff hz).mpr hzs)
  obtain ⟨n, hn, hchain⟩ := hzs
  have hlow : 4 ≤ n := by
    by_contra hbad
    exact target_not_mem_S_four c π hz ⟨n, by omega, hchain⟩
  have hn4 : n = 4 := by omega
  have hi5 : i = 5 := by omega
  subst i
  have hchain4 : LayerSets.Chain (R c π) v 4 z := by
    simpa only [hn4] using hchain
  have hz4 : z ∈ Ti c π 4 :=
    (LayerSets.target_mem_T_iff hz).mpr (target_not_mem_S_four c π hz)
  exact ⟨rfl, hchain4, hz4, hzt⟩

/-- Every assigned edge for i=1,...,5 starts in the exact (i-1)-st layer. -/
theorem M_tail_layer (c : (G.induce {x | x ≠ v}).Coloring (Fin 4))
    (π : Equiv.Perm (Fin 4)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ 5)
    {e : V × V} (he : e ∈ M c π i) :
    LayerSets.Chain (R c π) v (i - 1) e.1 ∧
      e.1 ∈ Ti c π (i - 1) \ Ti c π i := by
  rcases e with ⟨x, y⟩
  rcases he with ⟨hx, hy, hxy⟩ | ⟨hxZ, _hy, hx⟩
  · have hb := LayerSets.boundary_exact_layer hxy hy hx
    exact ⟨hb.2.1, hb.2.2.2, hx⟩
  · exact (old_mono_tail c π hi.2 hxZ hx).2

end TaskH.LayerTail

#print axioms TaskH.LayerTail.chain_endColor
#print axioms TaskH.LayerTail.target_chain_length_dvd
#print axioms TaskH.LayerTail.target_not_mem_S_four
#print axioms TaskH.LayerTail.old_mono_tail
#print axioms TaskH.LayerTail.M_tail_layer
