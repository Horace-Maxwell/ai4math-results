import Research.TaskH.LowDegreeCycles

/-!
Actual cycles in G-v through each of the four neighbors, for each of the
three cyclic color orders, and their injective transport into G.
-/

set_option autoImplicit false

universe u w t

namespace TaskH

open Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem fourColorCycle_predecessor_four (j : Fin 3) (i : Fin 4) :
    (fourColorCycle j).symm ((fourColorCycle j).symm
      ((fourColorCycle j).symm ((fourColorCycle j).symm i))) = i := by
  have h : ∀ (j : Fin 3) (i : Fin 4),
      (fourColorCycle j).symm ((fourColorCycle j).symm
        ((fourColorCycle j).symm ((fourColorCycle j).symm i))) = i := by decide +kernel
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
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (x : V) : Fin 4 := by
  classical
  exact if hx : x = v then 0 else c ⟨x, hx⟩

theorem deletedColorExtension_outside (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (x : V) (hx : x ≠ v) :
    deletedColorExtension v c x = c ⟨x, hx⟩ := by
  classical
  simp only [deletedColorExtension, dite_eq_right hx]

section FiniteGraph

variable [Fintype V] [DecidableRel G.Adj]

theorem degreeFour_deleted_follows_cycle (hcrit : IsCriticalPlus 4 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) :
    ∃ q : (G.induce {x | x ≠ v}).Walk
      (degreeFourNeighbor hcrit v c hdegree i) (degreeFourNeighbor hcrit v c hdegree i),
      q.IsCycle ∧ Follows q c (fourColorCycle j) := by
  let σ := fourColorCycle j
  have h0 := degreeFourNeighbor_reachable hcrit v c hdegree σ i
  have h1 := degreeFourNeighbor_reachable hcrit v c hdegree σ (σ.symm i)
  have h2 := degreeFourNeighbor_reachable hcrit v c hdegree σ (σ.symm (σ.symm i))
  have h3 := degreeFourNeighbor_reachable hcrit v c hdegree σ
    (σ.symm (σ.symm (σ.symm i)))
  have hpred4 : σ.symm (σ.symm (σ.symm (σ.symm i))) = i :=
    fourColorCycle_predecessor_four j i
  have hback' := h1.trans (h2.trans h3)
  have hback : Relation.ReflTransGen (ColorStep (G.induce {x | x ≠ v}) c σ)
      (degreeFourNeighbor hcrit v c hdegree (σ.symm i))
      (degreeFourNeighbor hcrit v c hdegree i) := by
    simpa only [hpred4] using hback'
  obtain ⟨P, hP⟩ := reach_exists_follows_walk c σ h0
  obtain ⟨Q, hQ⟩ := reach_exists_follows_walk c σ hback
  have hcolors_ne : i ≠ σ.symm i := by
    intro he
    exact fourColorCycle_no_fixed j i ((congrArg σ he).trans (σ.apply_symm_apply i))
  have hverts_ne : degreeFourNeighbor hcrit v c hdegree i ≠
      degreeFourNeighbor hcrit v c hdegree (σ.symm i) := by
    intro he
    apply hcolors_ne
    calc
      i = c (degreeFourNeighbor hcrit v c hdegree i) :=
        (degreeFourNeighbor_color hcrit v c hdegree i).symm
      _ = c (degreeFourNeighbor hcrit v c hdegree (σ.symm i)) := congrArg c he
      _ = σ.symm i := degreeFourNeighbor_color hcrit v c hdegree (σ.symm i)
  have hpos : 0 < P.length := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hverts_ne)
  have hnon : P.append Q ≠ .nil := by
    intro he
    have hz := congrArg Walk.length he
    simp only [Walk.length_append, Walk.length_nil] at hz
    omega
  have hf := (follows_append P Q c σ).mpr ⟨hP, hQ⟩
  exact follows_closed_exists_cycle (P.append Q) hnon c σ hf
    (fourColorCycle_no_two_step j (c (degreeFourNeighbor hcrit v c hdegree i)))

/-- The H-cycle is transported into the actual original graph, remains a
genuine cycle, follows the original deleted colors, and avoids v. -/
theorem degreeFour_avoid_cycle (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) :
    ∃ p : G.Walk (degreeFourNeighbor hcrit v c hdegree i).val
      (degreeFourNeighbor hcrit v c hdegree i).val,
      p.IsCycle ∧ p.length = 4 ∧ Follows p (deletedColorExtension v c) (fourColorCycle j) ∧
        v ∉ p.support := by
  obtain ⟨q, hq, hqf⟩ := degreeFour_deleted_follows_cycle hcrit v c hdegree i j
  let e : G.induce {x | x ≠ v} ↪g G := Embedding.induce {x | x ≠ v}
  let p := q.map e.toHom
  have hp : p.IsCycle := (Walk.isCycle_map_iff_of_injective e.injective).mpr hq
  have hdiv : 4 ∣ p.length := by
    simpa only [p, Walk.length_map] using follows_fourColorCycle_length_dvd q c j hqf
  have hlen : p.length = 4 := hs p hp hdiv
  have hpF : Follows p (deletedColorExtension v c) (fourColorCycle j) := by
    apply follows_map_of_colors e.toHom c (deletedColorExtension v c) (fourColorCycle j) ?_ q hqf
    intro z
    exact deletedColorExtension_outside v c z.val z.property
  refine ⟨p, hp, hlen, hpF, ?_⟩
  intro hv
  change v ∈ (q.map e.toHom).support at hv
  rw [Walk.support_map] at hv
  obtain ⟨z, _, he⟩ := List.mem_map.mp hv
  exact z.property he

noncomputable def degreeFourAvoidCycle (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) :
    G.Walk (degreeFourNeighbor hcrit v c hdegree i).val
      (degreeFourNeighbor hcrit v c hdegree i).val :=
  Classical.choose (degreeFour_avoid_cycle hcrit hs v c hdegree i j)

theorem degreeFourAvoidCycle_isCycle (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) : (degreeFourAvoidCycle hcrit hs v c hdegree i j).IsCycle :=
  (Classical.choose_spec (degreeFour_avoid_cycle hcrit hs v c hdegree i j)).1

theorem degreeFourAvoidCycle_length (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) : (degreeFourAvoidCycle hcrit hs v c hdegree i j).length = 4 :=
  (Classical.choose_spec (degreeFour_avoid_cycle hcrit hs v c hdegree i j)).2.1

theorem degreeFourAvoidCycle_follows (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) : Follows (degreeFourAvoidCycle hcrit hs v c hdegree i j)
      (deletedColorExtension v c) (fourColorCycle j) :=
  (Classical.choose_spec (degreeFour_avoid_cycle hcrit hs v c hdegree i j)).2.2.1

theorem degreeFourAvoidCycle_avoids (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) : v ∉ (degreeFourAvoidCycle hcrit hs v c hdegree i j).support :=
  (Classical.choose_spec (degreeFour_avoid_cycle hcrit hs v c hdegree i j)).2.2.2

end FiniteGraph

end TaskH

#print axioms TaskH.follows_map_of_colors
#print axioms TaskH.degreeFour_deleted_follows_cycle
#print axioms TaskH.degreeFour_avoid_cycle
#print axioms TaskH.degreeFourAvoidCycle_follows
