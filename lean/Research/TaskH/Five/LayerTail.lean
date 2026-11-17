import Research.TaskH.Five.LayerColoring
import Research.TaskH.Five.ColorCycle

/-!
Exact tail layers for every assigned shifted-monochromatic edge.
The old root-edge case derives its distance from the genuine five-color
successor relation; no distance premise is added to the coloring data.
-/

universe u

namespace TaskH.Five.LayerTail

open SimpleGraph _root_.TaskH.Five.LayerColoring

variable {V : Type u} {G : SimpleGraph V} {v : V}

/-- Returning from label 4 to label 4 takes a multiple of five successor steps. -/
theorem target_chain_length_dvd (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {z : V} {n : ℕ} (hz : z ∈ Z c π)
    (hchain : LayerSets.Chain (R c π) v n z) : 5 ∣ n := by
  have hc := TaskH.LayerTail.chain_endColor (baseColor c π) (finRotate 5) hchain
  rw [baseColor_root] at hc
  have hfix : ((finRotate 5) ^ n) (4 : Fin 5) = 4 := hc.symm.trans hz.2
  apply (TaskH.Five.rotate_pow_fixed_iff (4 : Fin 5) n).mp
  exact hfix

/-- No original monochromatic root neighbor is reached in fewer than five steps. -/
theorem target_not_mem_S_five (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {z : V} (hz : z ∈ Z c π) :
    z ∉ LayerSets.S (R c π) v 5 := by
  rintro ⟨n, hn, hchain⟩
  have hdiv := target_chain_length_dvd c π hz hchain
  have hnzero : n = 0 := by
    obtain ⟨m, hm⟩ := hdiv
    omega
  subst n
  exact hz.1.ne (TaskH.LayerTail.chain_end_eq_of_zero hchain).symm

/-- A surviving old monochromatic root edge occurs only at layer six. -/
theorem old_mono_tail (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i : ℕ} (hi : i ≤ 6) {z : V}
    (hz : z ∈ Z c π) (hzt : z ∉ Ti c π i) :
    i = 6 ∧ LayerSets.Chain (R c π) v (i - 1) z ∧
      z ∈ Ti c π (i - 1) \ Ti c π i := by
  classical
  have hzs : z ∈ LayerSets.S (R c π) v i := by
    by_contra hzs
    exact hzt ((LayerSets.target_mem_T_iff hz).mpr hzs)
  obtain ⟨n, hn, hchain⟩ := hzs
  have hlow : 5 ≤ n := by
    by_contra hbad
    exact target_not_mem_S_five c π hz ⟨n, by omega, hchain⟩
  have hn5 : n = 5 := by omega
  have hi6 : i = 6 := by omega
  subst i
  have hchain5 : LayerSets.Chain (R c π) v 5 z := by
    simpa only [hn5] using hchain
  have hz5 : z ∈ Ti c π 5 :=
    (LayerSets.target_mem_T_iff hz).mpr (target_not_mem_S_five c π hz)
  exact ⟨rfl, hchain5, hz5, hzt⟩

/-- Every assigned edge for i=1,...,6 starts in the exact (i-1)-st layer. -/
theorem M_tail_layer (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ 6)
    {e : V × V} (he : e ∈ M c π i) :
    LayerSets.Chain (R c π) v (i - 1) e.1 ∧
      e.1 ∈ Ti c π (i - 1) \ Ti c π i := by
  rcases e with ⟨x, y⟩
  rcases he with ⟨hx, hy, hxy⟩ | ⟨hxZ, _hy, hx⟩
  · have hb := LayerSets.boundary_exact_layer hxy hy hx
    exact ⟨hb.2.1, hb.2.2.2, hx⟩
  · exact (old_mono_tail c π hi.2 hxZ hx).2

end TaskH.Five.LayerTail


#print axioms TaskH.Five.LayerTail.target_chain_length_dvd
#print axioms TaskH.Five.LayerTail.target_not_mem_S_five
#print axioms TaskH.Five.LayerTail.old_mono_tail
#print axioms TaskH.Five.LayerTail.M_tail_layer
