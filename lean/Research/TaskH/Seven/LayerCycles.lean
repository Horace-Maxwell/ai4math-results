import Research.TaskH.Seven.LayerTail
import Research.TaskH.MonochromaticReach

/-!
For each layer i=1,...,8, construct a genuine simple cycle through a tail
in T_(i-1) minus T_i, following the shifted seven-color successor relation.
Distinctness of these edge sets and their good-order flux are separate tasks.
-/

universe u

namespace TaskH.Seven.LayerCycles

open SimpleGraph _root_.TaskH.Seven.LayerColoring _root_.TaskH.Seven.LayerTail

variable {V : Type u} {G : SimpleGraph V} {v : V}

/-- Every assigned head reaches the root in the shifted successor relation. -/
theorem head_reaches_root (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {i : ℕ} (hi : 1 ≤ i)
    {f : V × V} (hf : f ∈ M c π i) :
    Relation.ReflTransGen (ColorStep G (shiftedColor c π i) (finRotate 7)) f.2 v := by
  rcases hf with ⟨_hx, hy, _hxy⟩ | ⟨_hz, hroot, _hx⟩
  · obtain ⟨z, hz, hzT, hpath⟩ :=
      LayerSets.mem_T_exists_inside_path (R := R c π) (root := v) (Z := Z c π) hy
    have hr := reach_preserved_inside c π hpath
    have hlast : ColorStep G (shiftedColor c π i) (finRotate 7) z v := by
      refine ⟨hz.1.symm, ?_⟩
      rw [shiftedColor_outside c π (root_not_mem_Ti c π hi), baseColor_root,
        shiftedColor_inside c π hzT, hz.2, Equiv.apply_symm_apply]
    exact hr.tail hlast
  · rw [hroot]

/-- The actual short root chain to each assigned tail survives outside T_i. -/
theorem root_reaches_tail (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ 8)
    {e : V × V} (he : e ∈ M c π i) :
    Relation.ReflTransGen (ColorStep G (shiftedColor c π i) (finRotate 7)) v e.1 := by
  have hchain := (M_tail_layer c π hi he).1
  have hshort : i - 1 < i := by omega
  have hout : LayerSets.Chain (LayerSets.AvoidStep (R c π) (Ti c π i))
      v (i - 1) e.1 :=
    LayerSets.Chain.avoids_T_of_short (Z := Z c π) hchain hshort
  exact (chain_preserved_outside c π hout).to_reflTransGen

/-- A layer tail differs from every assigned head in the same layer. -/
theorem tail_ne_head (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ 8)
    {e f : V × V} (he : e ∈ M c π i) (hf : f ∈ M c π i) : e.1 ≠ f.2 := by
  have htail := (M_tail_layer c π hi he).2
  intro heq
  rcases hf with ⟨_hx, hy, _hxy⟩ | ⟨hfZ, hfroot, hfout⟩
  · apply htail.2
    rw [heq]
    exact hy
  · have hi6 := (old_mono_tail c π hi.2 hfZ hfout).1
    apply root_not_mem_Ti c π (by decide : 1 ≤ 7)
    simpa only [hi6, heq, hfroot] using htail.1

/-- First narrow walk form of the head-to-root transport. -/
theorem head_exists_follows_walk (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {i : ℕ} (hi : 1 ≤ i)
    {f : V × V} (hf : f ∈ M c π i) :
    ∃ p : G.Walk f.2 v, Follows p (shiftedColor c π i) (finRotate 7) :=
  reach_exists_follows_walk _ _ (head_reaches_root c π hi hf)

/-- First narrow walk form of the root-to-tail transport. -/
theorem root_exists_follows_walk (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ 8)
    {e : V × V} (he : e ∈ M c π i) :
    ∃ p : G.Walk v e.1, Follows p (shiftedColor c π i) (finRotate 7) :=
  reach_exists_follows_walk _ _ (root_reaches_tail c π hi he)

/-- The original recoloring construction yields a genuine cycle at every layer. -/
theorem exists_layer_cycle (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (hnot : ¬ G.Colorable 7)
    {i : ℕ} (hi : 1 ≤ i ∧ i ≤ 8) :
    ∃ t : V, t ∈ Ti c π (i - 1) \ Ti c π i ∧
      ∃ p : G.Walk t t, p.IsCycle ∧ Follows p (shiftedColor c π i) (finRotate 7) := by
  obtain ⟨e, he, f, hf, hreach⟩ :=
    noncolorable_reach_between_monoEdges hnot (shiftedColor c π i) (finRotate 7) (M c π i)
      (by
        intro _x _y hxy heq
        exact shifted_mono_cover c π hi.1 hxy heq)
  obtain ⟨p, hp⟩ := reach_exists_follows_walk (shiftedColor c π i) (finRotate 7) hreach
  obtain ⟨q, hq⟩ := head_exists_follows_walk c π hi.1 hf
  obtain ⟨r, hr⟩ := root_exists_follows_walk c π hi he
  let w : G.Walk e.1 e.1 := (p.append q).append r
  have hw : Follows w (shiftedColor c π i) (finRotate 7) :=
    (follows_append _ _ _ _).mpr ⟨(follows_append _ _ _ _).mpr ⟨hp, hq⟩, hr⟩
  have hne : e.1 ≠ f.2 := tail_ne_head c π hi he hf
  have hwnil : w ≠ .nil := by
    intro hnil
    have hzero : w.length = 0 := by simp only [hnil, Walk.length_nil]
    change ((p.append q).append r).length = 0 at hzero
    simp only [Walk.length_append] at hzero
    have hpzero : p.length = 0 := by omega
    exact hne (Walk.eq_of_length_eq_zero hpzero)
  have htwo : (finRotate 7) ((finRotate 7) (shiftedColor c π i e.1)) ≠
      shiftedColor c π i e.1 :=
    TaskH.Seven.rotate_no_two_step (shiftedColor c π i e.1)
  obtain ⟨pcycle, hcycle, hfollow⟩ :=
    follows_closed_exists_cycle w hwnil (shiftedColor c π i) (finRotate 7) hw htwo
  exact ⟨e.1, (M_tail_layer c π hi he).2, pcycle, hcycle, hfollow⟩

end TaskH.Seven.LayerCycles


#print axioms TaskH.Seven.LayerCycles.head_reaches_root
#print axioms TaskH.Seven.LayerCycles.root_reaches_tail
#print axioms TaskH.Seven.LayerCycles.tail_ne_head
#print axioms TaskH.Seven.LayerCycles.head_exists_follows_walk
#print axioms TaskH.Seven.LayerCycles.root_exists_follows_walk
#print axioms TaskH.Seven.LayerCycles.exists_layer_cycle
