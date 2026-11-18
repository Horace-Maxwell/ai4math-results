import Research.TaskH.General.LayerColoring
import Research.TaskH.General.ColorCycle
import Research.TaskH.DirectedCycle
import Research.TaskH.MonochromaticReach

/-!
For each actual layer 1 <= i <= k+1, produce a genuine simple cycle in G.
The old-root-edge tail distance is derived from the actual k-rotation order.
Layer distinctness and good-order flux are still separate obligations.
-/

universe u

namespace TaskH.General.LayerCycles

open SimpleGraph _root_.TaskH.General.LayerColoring

variable {V : Type u} {G : SimpleGraph V} {v : V} {k : ℕ} (hk : 3 ≤ k)

/-- Returning from the last label to itself takes a multiple of k successor steps. -/
theorem target_chain_length_dvd (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) {z : V} {n : ℕ} (hz : z ∈ Z hk c π)
    (hchain : LayerSets.Chain (R hk c π) v n z) : k ∣ n := by
  have hc : baseColor hk c π z = ((finRotate k) ^ n) (baseColor hk c π v) := by
    clear hz
    change LayerSets.Chain (ColorStep G (baseColor hk c π) (finRotate k)) v n z at hchain
    induction hchain with
    | nil => rfl
    | @tail n a b _ hab ih =>
      calc
        baseColor hk c π b = finRotate k (baseColor hk c π a) := hab.2
        _ = finRotate k (((finRotate k) ^ n) (baseColor hk c π v)) :=
          congrArg (finRotate k) ih
        _ = ((finRotate k) ^ (n + 1)) (baseColor hk c π v) := by
          rw [pow_succ']
          rfl
  rw [baseColor_root] at hc
  have hfix : ((finRotate k) ^ n) (rootLabel hk) = rootLabel hk := hc.symm.trans hz.2
  apply (TaskH.General.rotate_pow_fixed_iff hk (rootLabel hk) n).mp
  exact hfix

/-- No original monochromatic root neighbor is reached in fewer than k steps. -/
theorem target_not_mem_S_k (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) {z : V} (hz : z ∈ Z hk c π) :
    z ∉ LayerSets.S (R hk c π) v k := by
  rintro ⟨n, hn, hchain⟩
  have hdiv := target_chain_length_dvd hk c π hz hchain
  have hnzero : n = 0 := by
    by_contra hnzero
    have hle : k ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hnzero) hdiv
    omega
  subst n
  have hroot : z = v := by
    cases hchain
    rfl
  exact hz.1.ne hroot.symm

/-- A surviving old monochromatic root edge occurs only at layer k+1. -/
theorem old_mono_tail (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) {i : ℕ} (hi : i ≤ k + 1) {z : V}
    (hz : z ∈ Z hk c π) (hzt : z ∉ Ti hk c π i) :
    i = k + 1 ∧ LayerSets.Chain (R hk c π) v (i - 1) z ∧
      z ∈ Ti hk c π (i - 1) \ Ti hk c π i := by
  classical
  have hzs : z ∈ LayerSets.S (R hk c π) v i := by
    by_contra hzs
    exact hzt ((LayerSets.target_mem_T_iff hz).mpr hzs)
  obtain ⟨n, hn, hchain⟩ := hzs
  have hlow : k ≤ n := by
    by_contra hbad
    exact target_not_mem_S_k hk c π hz ⟨n, by omega, hchain⟩
  have hn5 : n = k := by omega
  have hi6 : i = k + 1 := by omega
  subst i
  have hchain5 : LayerSets.Chain (R hk c π) v k z := by
    simpa only [hn5] using hchain
  have hz5 : z ∈ Ti hk c π k :=
    (LayerSets.target_mem_T_iff hz).mpr (target_not_mem_S_k hk c π hz)
  exact ⟨rfl, by simpa only [Nat.add_sub_cancel] using hchain5,
    by simpa only [Nat.add_sub_cancel] using hz5, hzt⟩

/-- Every assigned edge for i=1,...,k+1 starts in the exact (i-1)-st layer. -/
theorem M_tail_layer (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ k + 1)
    {e : V × V} (he : e ∈ M hk c π i) :
    LayerSets.Chain (R hk c π) v (i - 1) e.1 ∧
      e.1 ∈ Ti hk c π (i - 1) \ Ti hk c π i := by
  rcases e with ⟨x, y⟩
  rcases he with ⟨hx, hy, hxy⟩ | ⟨hxZ, _hy, hx⟩
  · have hb := LayerSets.boundary_exact_layer hxy hy hx
    exact ⟨hb.2.1, hb.2.2.2, hx⟩
  · exact (old_mono_tail hk c π hi.2 hxZ hx).2

/-- Every assigned head reaches the root in the shifted successor relation. -/
theorem head_reaches_root (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) {i : ℕ} (hi : 1 ≤ i)
    {f : V × V} (hf : f ∈ M hk c π i) :
    Relation.ReflTransGen (ColorStep G (shiftedColor hk c π i) (finRotate k)) f.2 v := by
  rcases hf with ⟨_hx, hy, _hxy⟩ | ⟨_hz, hroot, _hx⟩
  · obtain ⟨z, hz, hzT, hpath⟩ :=
      LayerSets.mem_T_exists_inside_path (R := R hk c π) (root := v) (Z := Z hk c π) hy
    have hr := reach_preserved_inside hk c π hpath
    have hlast : ColorStep G (shiftedColor hk c π i) (finRotate k) z v := by
      refine ⟨hz.1.symm, ?_⟩
      rw [shiftedColor_outside hk c π (root_not_mem_Ti hk c π hi), baseColor_root,
        shiftedColor_inside hk c π hzT, hz.2, Equiv.apply_symm_apply]
    exact hr.tail hlast
  · rw [hroot]

/-- The actual short root chain to each assigned tail survives outside T_i. -/
theorem root_reaches_tail (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ k + 1)
    {e : V × V} (he : e ∈ M hk c π i) :
    Relation.ReflTransGen (ColorStep G (shiftedColor hk c π i) (finRotate k)) v e.1 := by
  have hchain := (M_tail_layer hk c π hi he).1
  have hshort : i - 1 < i := by omega
  have hout : LayerSets.Chain (LayerSets.AvoidStep (R hk c π) (Ti hk c π i))
      v (i - 1) e.1 :=
    LayerSets.Chain.avoids_T_of_short (Z := Z hk c π) hchain hshort
  exact (chain_preserved_outside hk c π hout).to_reflTransGen

/-- A layer tail differs from every assigned head in the same layer. -/
theorem tail_ne_head (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ k + 1)
    {e f : V × V} (he : e ∈ M hk c π i) (hf : f ∈ M hk c π i) : e.1 ≠ f.2 := by
  have htail := (M_tail_layer hk c π hi he).2
  intro heq
  rcases hf with ⟨_hx, hy, _hxy⟩ | ⟨hfZ, hfroot, hfout⟩
  · apply htail.2
    rw [heq]
    exact hy
  · have hi6 := (old_mono_tail hk c π hi.2 hfZ hfout).1
    apply root_not_mem_Ti hk c π (by omega : 1 ≤ k)
    simpa only [hi6, heq, hfroot, Nat.add_sub_cancel] using htail.1

/-- First narrow walk form of the head-to-root transport. -/
theorem head_exists_follows_walk (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) {i : ℕ} (hi : 1 ≤ i)
    {f : V × V} (hf : f ∈ M hk c π i) :
    ∃ p : G.Walk f.2 v, Follows p (shiftedColor hk c π i) (finRotate k) :=
  reach_exists_follows_walk _ _ (head_reaches_root hk c π hi hf)

/-- First narrow walk form of the root-to-tail transport. -/
theorem root_exists_follows_walk (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ k + 1)
    {e : V × V} (he : e ∈ M hk c π i) :
    ∃ p : G.Walk v e.1, Follows p (shiftedColor hk c π i) (finRotate k) :=
  reach_exists_follows_walk _ _ (root_reaches_tail hk c π hi he)

/-- The original recoloring construction yields a genuine cycle at every layer. -/
theorem exists_layer_cycle (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) (hnot : ¬ G.Colorable k)
    {i : ℕ} (hi : 1 ≤ i ∧ i ≤ k + 1) :
    ∃ t : V, t ∈ Ti hk c π (i - 1) \ Ti hk c π i ∧
      ∃ p : G.Walk t t, p.IsCycle ∧ Follows p (shiftedColor hk c π i) (finRotate k) := by
  obtain ⟨e, he, f, hf, hreach⟩ :=
    noncolorable_reach_between_monoEdges hnot (shiftedColor hk c π i) (finRotate k) (M hk c π i)
      (by
        intro _x _y hxy heq
        exact shifted_mono_cover hk c π hi.1 hxy heq)
  obtain ⟨p, hp⟩ := reach_exists_follows_walk (shiftedColor hk c π i) (finRotate k) hreach
  obtain ⟨q, hq⟩ := head_exists_follows_walk hk c π hi.1 hf
  obtain ⟨r, hr⟩ := root_exists_follows_walk hk c π hi he
  let w : G.Walk e.1 e.1 := (p.append q).append r
  have hw : Follows w (shiftedColor hk c π i) (finRotate k) :=
    (follows_append _ _ _ _).mpr ⟨(follows_append _ _ _ _).mpr ⟨hp, hq⟩, hr⟩
  have hne : e.1 ≠ f.2 := tail_ne_head hk c π hi he hf
  have hwnil : w ≠ .nil := by
    intro hnil
    have hzero : w.length = 0 := by simp only [hnil, Walk.length_nil]
    change ((p.append q).append r).length = 0 at hzero
    simp only [Walk.length_append] at hzero
    have hpzero : p.length = 0 := by omega
    exact hne (Walk.eq_of_length_eq_zero hpzero)
  have htwo : (finRotate k) ((finRotate k) (shiftedColor hk c π i e.1)) ≠
      shiftedColor hk c π i e.1 :=
    TaskH.General.rotate_no_two_step hk (shiftedColor hk c π i e.1)
  obtain ⟨pcycle, hcycle, hfollow⟩ :=
    follows_closed_exists_cycle w hwnil (shiftedColor hk c π i) (finRotate k) hw htwo
  exact ⟨e.1, (M_tail_layer hk c π hi he).2, pcycle, hcycle, hfollow⟩

/-- Original proper-subgraph criticality supplies one actual deleted-vertex
coloring, and that same coloring yields a genuine cycle at every required layer. -/
theorem critical_exists_coloring_layer_cycles (hcrit : Challenge.IsCriticalPlus k G)
    (v : V) (π : Equiv.Perm (Fin k)) :
    ∃ c : (G.induce {x | x ≠ v}).Coloring (Fin k),
      ∀ i : ℕ, 1 ≤ i ∧ i ≤ k + 1 →
        ∃ t : V, t ∈ Ti hk c π (i - 1) \ Ti hk c π i ∧
          ∃ p : G.Walk t t, p.IsCycle ∧ Follows p (shiftedColor hk c π i) (finRotate k) := by
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  refine ⟨c, ?_⟩
  intro i hi
  exact exists_layer_cycle hk c π (critical_not_colorable hcrit) hi

end TaskH.General.LayerCycles

#print axioms TaskH.General.LayerCycles.target_chain_length_dvd
#print axioms TaskH.General.LayerCycles.target_not_mem_S_k
#print axioms TaskH.General.LayerCycles.old_mono_tail
#print axioms TaskH.General.LayerCycles.M_tail_layer
#print axioms TaskH.General.LayerCycles.head_reaches_root
#print axioms TaskH.General.LayerCycles.root_reaches_tail
#print axioms TaskH.General.LayerCycles.tail_ne_head
#print axioms TaskH.General.LayerCycles.head_exists_follows_walk
#print axioms TaskH.General.LayerCycles.root_exists_follows_walk
#print axioms TaskH.General.LayerCycles.exists_layer_cycle

#print axioms TaskH.General.LayerCycles.critical_exists_coloring_layer_cycles
