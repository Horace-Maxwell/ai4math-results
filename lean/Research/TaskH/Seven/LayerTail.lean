import Research.TaskH.Seven.LayerColoring
import Research.TaskH.Seven.ColorCycle

/-!
Exact tail layers for every assigned shifted-monochromatic edge.
The old root-edge case derives its distance from the genuine seven-color
successor relation; no distance premise is added to the coloring data.
-/

universe u

namespace TaskH.Seven.LayerTail

open SimpleGraph _root_.TaskH.Seven.LayerColoring

variable {V : Type u} {G : SimpleGraph V} {v : V}

/-- Returning from label 6 to label 6 takes a multiple of seven successor steps. -/
theorem target_chain_length_dvd (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {z : V} {n : ℕ} (hz : z ∈ Z c π)
    (hchain : LayerSets.Chain (R c π) v n z) : 7 ∣ n := by
  have hc := TaskH.LayerTail.chain_endColor (baseColor c π) (finRotate 7) hchain
  rw [baseColor_root] at hc
  have hfix : ((finRotate 7) ^ n) (6 : Fin 7) = 6 := hc.symm.trans hz.2
  apply (TaskH.Seven.rotate_pow_fixed_iff (6 : Fin 7) n).mp
  exact hfix

/-- No original monochromatic root neighbor is reached in fewer than seven steps. -/
theorem target_not_mem_S_seven (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {z : V} (hz : z ∈ Z c π) :
    z ∉ LayerSets.S (R c π) v 7 := by
  rintro ⟨n, hn, hchain⟩
  have hdiv := target_chain_length_dvd c π hz hchain
  have hnzero : n = 0 := by
    obtain ⟨m, hm⟩ := hdiv
    omega
  subst n
  exact hz.1.ne (TaskH.LayerTail.chain_end_eq_of_zero hchain).symm

/-- A surviving old monochromatic root edge occurs only at layer eight. -/
theorem old_mono_tail (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {i : ℕ} (hi : i ≤ 8) {z : V}
    (hz : z ∈ Z c π) (hzt : z ∉ Ti c π i) :
    i = 8 ∧ LayerSets.Chain (R c π) v (i - 1) z ∧
      z ∈ Ti c π (i - 1) \ Ti c π i := by
  classical
  have hzs : z ∈ LayerSets.S (R c π) v i := by
    by_contra hzs
    exact hzt ((LayerSets.target_mem_T_iff hz).mpr hzs)
  obtain ⟨n, hn, hchain⟩ := hzs
  have hlow : 7 ≤ n := by
    by_contra hbad
    exact target_not_mem_S_seven c π hz ⟨n, by omega, hchain⟩
  have hn5 : n = 7 := by omega
  have hi6 : i = 8 := by omega
  subst i
  have hchain5 : LayerSets.Chain (R c π) v 7 z := by
    simpa only [hn5] using hchain
  have hz5 : z ∈ Ti c π 7 :=
    (LayerSets.target_mem_T_iff hz).mpr (target_not_mem_S_seven c π hz)
  exact ⟨rfl, hchain5, hz5, hzt⟩

/-- Every assigned edge for i=1,...,8 starts in the exact (i-1)-st layer. -/
theorem M_tail_layer (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ 8)
    {e : V × V} (he : e ∈ M c π i) :
    LayerSets.Chain (R c π) v (i - 1) e.1 ∧
      e.1 ∈ Ti c π (i - 1) \ Ti c π i := by
  rcases e with ⟨x, y⟩
  rcases he with ⟨hx, hy, hxy⟩ | ⟨hxZ, _hy, hx⟩
  · have hb := LayerSets.boundary_exact_layer hxy hy hx
    exact ⟨hb.2.1, hb.2.2.2, hx⟩
  · exact (old_mono_tail c π hi.2 hxZ hx).2

end TaskH.Seven.LayerTail


#print axioms TaskH.Seven.LayerTail.target_chain_length_dvd
#print axioms TaskH.Seven.LayerTail.target_not_mem_S_seven
#print axioms TaskH.Seven.LayerTail.old_mono_tail
#print axioms TaskH.Seven.LayerTail.M_tail_layer
