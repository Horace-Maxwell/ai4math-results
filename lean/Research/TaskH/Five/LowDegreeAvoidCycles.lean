import Research.TaskH.Five.LowDegreePaths
import Research.TaskH.Five.EdgeCycles

/-!
Actual cycles in G-v through each of the four neighbors, for each of the
three cyclic color orders, and their injective transport into G.
-/

set_option autoImplicit false

universe u w t

namespace TaskH.Five

open _root_.TaskH.Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem fiveColorCycle_predecessor_five (j : Fin 12) (i : Fin 5) :
    (fiveColorCycle j).symm ((fiveColorCycle j).symm
      ((fiveColorCycle j).symm ((fiveColorCycle j).symm ((fiveColorCycle j).symm i)))) = i := by
  have h : ∀ (j : Fin 12) (i : Fin 5),
      (fiveColorCycle j).symm ((fiveColorCycle j).symm
        ((fiveColorCycle j).symm ((fiveColorCycle j).symm ((fiveColorCycle j).symm i)))) = i := by
    decide +kernel
  exact h j i

theorem follows_map_of_colors {W : Type w} {H : SimpleGraph W} {α : Type t}
    (f : H →g G) (a : W → α) (b : V → α) (σ : Equiv.Perm α)
    (hcolors : ∀ z : W, b (f z) = a z) {x y : W} (p : H.Walk x y)
    (hf : Follows p a σ) : Follows (p.map f) b σ := by
  revert hf
  induction p with
  | nil => intro _; exact follows_nil _ _ _
  | @cons x y z h p ih =>
    intro hf
    have hp := (follows_cons h p a σ).mp hf
    apply (follows_cons (f.map_adj h) (p.map f) b σ).mpr
    exact ⟨by simpa only [hcolors] using hp.1, ih hp.2⟩

/-- One common full-vertex labeling for all cycles avoiding v. -/
noncomputable def deletedColorExtension (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (x : V) : Fin 5 := by
  classical
  exact if hx : x = v then 0 else c ⟨x, hx⟩

theorem deletedColorExtension_outside (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (x : V) (hx : x ≠ v) :
    deletedColorExtension v c x = c ⟨x, hx⟩ := by
  classical
  simp only [deletedColorExtension, dite_eq_right hx]

section FiniteGraph

variable [Fintype V] [DecidableRel G.Adj]

theorem degreeFive_deleted_follows_cycle (hcrit : IsCriticalPlus 5 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) (j : Fin 12) :
    ∃ q : (G.induce {x | x ≠ v}).Walk
      (degreeFiveNeighbor hcrit v c hdegree i) (degreeFiveNeighbor hcrit v c hdegree i),
      q.IsCycle ∧ Follows q c (fiveColorCycle j) := by
  let σ := fiveColorCycle j
  have h0 := degreeFiveNeighbor_reachable hcrit v c hdegree σ i
  have h1 := degreeFiveNeighbor_reachable hcrit v c hdegree σ (σ.symm i)
  have h2 := degreeFiveNeighbor_reachable hcrit v c hdegree σ (σ.symm (σ.symm i))
  have h3 := degreeFiveNeighbor_reachable hcrit v c hdegree σ
    (σ.symm (σ.symm (σ.symm i)))
  have h4 := degreeFiveNeighbor_reachable hcrit v c hdegree σ
    (σ.symm (σ.symm (σ.symm (σ.symm i))))
  have hpred5 : σ.symm (σ.symm (σ.symm (σ.symm (σ.symm i)))) = i :=
    fiveColorCycle_predecessor_five j i
  have hback' := h1.trans (h2.trans (h3.trans h4))
  have hback : Relation.ReflTransGen (ColorStep (G.induce {x | x ≠ v}) c σ)
      (degreeFiveNeighbor hcrit v c hdegree (σ.symm i))
      (degreeFiveNeighbor hcrit v c hdegree i) := by
    simpa only [hpred5] using hback'
  obtain ⟨P, hP⟩ := reach_exists_follows_walk c σ h0
  obtain ⟨Q, hQ⟩ := reach_exists_follows_walk c σ hback
  have hcolors_ne : i ≠ σ.symm i := by
    intro he
    exact fiveColorCycle_no_fixed j i ((congrArg σ he).trans (σ.apply_symm_apply i))
  have hverts_ne : degreeFiveNeighbor hcrit v c hdegree i ≠
      degreeFiveNeighbor hcrit v c hdegree (σ.symm i) := by
    intro he
    apply hcolors_ne
    calc
      i = c (degreeFiveNeighbor hcrit v c hdegree i) :=
        (degreeFiveNeighbor_color hcrit v c hdegree i).symm
      _ = c (degreeFiveNeighbor hcrit v c hdegree (σ.symm i)) := congrArg c he
      _ = σ.symm i := degreeFiveNeighbor_color hcrit v c hdegree (σ.symm i)
  have hpos : 0 < P.length := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hverts_ne)
  have hnon : P.append Q ≠ .nil := by
    intro he
    have hz := congrArg Walk.length he
    simp only [Walk.length_append, Walk.length_nil] at hz
    omega
  have hf := (follows_append P Q c σ).mpr ⟨hP, hQ⟩
  exact follows_closed_exists_cycle (P.append Q) hnon c σ hf
    (fiveColorCycle_no_two_step j (c (degreeFiveNeighbor hcrit v c hdegree i)))

/-- The H-cycle is transported into the actual original graph, remains a
genuine cycle, follows the original deleted colors, and avoids v. -/
theorem degreeFive_avoid_cycle (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) (j : Fin 12) :
    ∃ p : G.Walk (degreeFiveNeighbor hcrit v c hdegree i).val
      (degreeFiveNeighbor hcrit v c hdegree i).val,
      p.IsCycle ∧ p.length = 5 ∧ Follows p (deletedColorExtension v c) (fiveColorCycle j) ∧
        v ∉ p.support := by
  obtain ⟨q, hq, hqf⟩ := degreeFive_deleted_follows_cycle hcrit v c hdegree i j
  let e : G.induce {x | x ≠ v} ↪g G := Embedding.induce {x | x ≠ v}
  let p := q.map e.toHom
  have hp : p.IsCycle := (Walk.isCycle_map_iff_of_injective e.injective).mpr hq
  have hdiv : 5 ∣ p.length := by
    simpa only [p, Walk.length_map] using follows_fiveColorCycle_length_dvd q c j hqf
  have hlen : p.length = 5 := hs p hp hdiv
  have hpF : Follows p (deletedColorExtension v c) (fiveColorCycle j) := by
    apply follows_map_of_colors e.toHom c (deletedColorExtension v c) (fiveColorCycle j) ?_ q hqf
    intro z
    exact deletedColorExtension_outside v c z.val z.property
  refine ⟨p, hp, hlen, hpF, ?_⟩
  intro hv
  change v ∈ (q.map e.toHom).support at hv
  rw [Walk.support_map] at hv
  obtain ⟨z, _, he⟩ := List.mem_map.mp hv
  exact z.property he

noncomputable def degreeFiveAvoidCycle (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) (j : Fin 12) :
    G.Walk (degreeFiveNeighbor hcrit v c hdegree i).val
      (degreeFiveNeighbor hcrit v c hdegree i).val :=
  Classical.choose (degreeFive_avoid_cycle hcrit hs v c hdegree i j)

theorem degreeFiveAvoidCycle_isCycle (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) (j : Fin 12) : (degreeFiveAvoidCycle hcrit hs v c hdegree i j).IsCycle :=
  (Classical.choose_spec (degreeFive_avoid_cycle hcrit hs v c hdegree i j)).1

theorem degreeFiveAvoidCycle_length (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) (j : Fin 12) : (degreeFiveAvoidCycle hcrit hs v c hdegree i j).length = 5 :=
  (Classical.choose_spec (degreeFive_avoid_cycle hcrit hs v c hdegree i j)).2.1

theorem degreeFiveAvoidCycle_follows (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) (j : Fin 12) : Follows (degreeFiveAvoidCycle hcrit hs v c hdegree i j)
      (deletedColorExtension v c) (fiveColorCycle j) :=
  (Classical.choose_spec (degreeFive_avoid_cycle hcrit hs v c hdegree i j)).2.2.1

theorem degreeFiveAvoidCycle_avoids (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) (j : Fin 12) : v ∉ (degreeFiveAvoidCycle hcrit hs v c hdegree i j).support :=
  (Classical.choose_spec (degreeFive_avoid_cycle hcrit hs v c hdegree i j)).2.2.2

end FiniteGraph

end TaskH.Five

#print axioms TaskH.Five.fiveColorCycle_predecessor_five
#print axioms TaskH.Five.follows_map_of_colors
#print axioms TaskH.Five.deletedColorExtension
#print axioms TaskH.Five.deletedColorExtension_outside
#print axioms TaskH.Five.degreeFive_deleted_follows_cycle
#print axioms TaskH.Five.degreeFive_avoid_cycle
#print axioms TaskH.Five.degreeFiveAvoidCycle
#print axioms TaskH.Five.degreeFiveAvoidCycle_isCycle
#print axioms TaskH.Five.degreeFiveAvoidCycle_length
#print axioms TaskH.Five.degreeFiveAvoidCycle_follows
#print axioms TaskH.Five.degreeFiveAvoidCycle_avoids
