import Research.TaskH.LayerSets
import Research.TaskH.Recolor

/-!
Actual graph colorings used by the original good-cycle layer construction.

The root's label color is 4. This is distinct from its vertex-order value 5
in RawDescents.orderColor; no vertex order is defined or changed here.
-/

universe u

namespace TaskH.Five.LayerColoring

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {v : V}

/-- Extend the actual coloring of G-v, assigning label color 4 to v. -/
noncomputable def baseColor (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) (x : V) : Fin 5 := by
  classical
  exact if hx : x = v then 4 else π (c ⟨x, hx⟩)

theorem baseColor_root (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) : baseColor c π v = 4 := by
  classical
  simp [baseColor]

theorem baseColor_outside (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {x : V} (hx : x ≠ v) :
    baseColor c π x = π (c ⟨x, hx⟩) := by
  classical
  simp [baseColor, hx]

theorem baseColor_adj_ne_outside (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {x y : V} (hxy : G.Adj x y) (hx : x ≠ v) (hy : y ≠ v) :
    baseColor c π x ≠ baseColor c π y := by
  rw [baseColor_outside c π hx, baseColor_outside c π hy]
  intro he
  have hc : c ⟨x, hx⟩ ≠ c ⟨y, hy⟩ := c.valid hxy
  exact hc (π.injective he)

/-- The original monochromatic neighbors of the root. -/
noncomputable def Z (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) : Set V :=
  {z | G.Adj v z ∧ baseColor c π z = 4}

/-- All original monochromatic edges are precisely the root--Z edges. -/
theorem baseColor_mono_iff (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {x y : V} (hxy : G.Adj x y) :
    baseColor c π x = baseColor c π y ↔
      (x ∈ Z c π ∧ y = v) ∨ (y ∈ Z c π ∧ x = v) := by
  constructor
  · intro he
    by_cases hx : x = v
    · subst x
      refine Or.inr ⟨⟨hxy, ?_⟩, rfl⟩
      simpa only [baseColor_root] using he.symm
    · by_cases hy : y = v
      · subst y
        refine Or.inl ⟨⟨hxy.symm, ?_⟩, rfl⟩
        simpa only [baseColor_root] using he
      · exact (baseColor_adj_ne_outside c π hxy hx hy he).elim
  · rintro (⟨hx, rfl⟩ | ⟨hy, rfl⟩)
    · rw [baseColor_root]
      exact hx.2
    · rw [baseColor_root]
      exact hy.2.symm

theorem Z_nonempty (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) (hnot : ¬ G.Colorable 5) : (Z c π).Nonempty := by
  classical
  by_contra hZ
  apply hnot
  refine ⟨SimpleGraph.Coloring.mk (baseColor c π) ?_⟩
  intro x y hxy he
  rcases (baseColor_mono_iff c π hxy).mp he with ⟨hx, _⟩ | ⟨hy, _⟩
  · exact hZ ⟨x, hx⟩
  · exact hZ ⟨y, hy⟩

/-- Original directed color-successor edges. -/
noncomputable def R (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) : V → V → Prop :=
  ColorStep G (baseColor c π) (finRotate 5)

noncomputable def Ti (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) (i : ℕ) : Set V :=
  LayerSets.T (R c π) v (Z c π) i

theorem root_not_mem_Ti (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i : ℕ} (hi : 1 ≤ i) : v ∉ Ti c π i :=
  LayerSets.root_not_mem_T hi

/-- Decrease labels by one modulo five precisely on T_i. -/
noncomputable def shiftedColor (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) (i : ℕ) (x : V) : Fin 5 := by
  classical
  exact if x ∈ Ti c π i then (finRotate 5).symm (baseColor c π x) else baseColor c π x

theorem shiftedColor_inside (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i : ℕ} {x : V} (hx : x ∈ Ti c π i) :
    shiftedColor c π i x = (finRotate 5).symm (baseColor c π x) := by
  classical
  simp [shiftedColor, hx]

theorem shiftedColor_outside (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i : ℕ} {x : V} (hx : x ∉ Ti c π i) :
    shiftedColor c π i x = baseColor c π x := by
  classical
  simp [shiftedColor, hx]

/-- The assigned orientations of new boundary edges and old surviving root edges. -/
noncomputable def M (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) (i : ℕ) : Set (V × V) :=
  {e | (e.1 ∉ Ti c π i ∧ e.2 ∈ Ti c π i ∧ R c π e.1 e.2) ∨
    (e.1 ∈ Z c π ∧ e.2 = v ∧ e.1 ∉ Ti c π i)}

/-- Every actual shifted-monochromatic edge receives one of the required orientations. -/
theorem shifted_mono_cover (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i : ℕ} (hi : 1 ≤ i) {x y : V}
    (hxy : G.Adj x y) (he : shiftedColor c π i x = shiftedColor c π i y) :
    (x, y) ∈ M c π i ∨ (y, x) ∈ M c π i := by
  classical
  have hv := root_not_mem_Ti c π hi
  by_cases hx : x ∈ Ti c π i
  · by_cases hy : y ∈ Ti c π i
    · rw [shiftedColor_inside c π hx, shiftedColor_inside c π hy] at he
      have hbase := (finRotate 5).symm.injective he
      rcases (baseColor_mono_iff c π hxy).mp hbase with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact (hv hy).elim
      · exact (hv hx).elim
    · rw [shiftedColor_inside c π hx, shiftedColor_outside c π hy] at he
      have hstep : baseColor c π x = (finRotate 5) (baseColor c π y) := by
        simpa only [Equiv.apply_symm_apply] using congrArg (finRotate 5) he
      exact Or.inr (Or.inl ⟨hy, hx, hxy.symm, hstep⟩)
  · by_cases hy : y ∈ Ti c π i
    · rw [shiftedColor_outside c π hx, shiftedColor_inside c π hy] at he
      have hstep : baseColor c π y = (finRotate 5) (baseColor c π x) := by
        simpa only [Equiv.apply_symm_apply] using (congrArg (finRotate 5) he).symm
      exact Or.inl (Or.inl ⟨hx, hy, hxy, hstep⟩)
    · rw [shiftedColor_outside c π hx, shiftedColor_outside c π hy] at he
      rcases (baseColor_mono_iff c π hxy).mp he with ⟨hxZ, hyv⟩ | ⟨hyZ, hxv⟩
      · exact Or.inl (Or.inr ⟨hxZ, hyv, hx⟩)
      · exact Or.inr (Or.inr ⟨hyZ, hxv, hy⟩)

/-- Conversely, assigned oriented edges are real shifted-monochromatic graph edges. -/
theorem M_edge_mono (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i : ℕ} (hi : 1 ≤ i) {x y : V}
    (he : (x, y) ∈ M c π i) :
    G.Adj x y ∧ shiftedColor c π i x = shiftedColor c π i y := by
  rcases he with ⟨hx, hy, hxy, hstep⟩ | ⟨hxZ, rfl, hx⟩
  · refine ⟨hxy, ?_⟩
    rw [shiftedColor_outside c π hx, shiftedColor_inside c π hy, hstep,
      Equiv.symm_apply_apply]
  · refine ⟨hxZ.1.symm, ?_⟩
    rw [shiftedColor_outside c π hx,
      shiftedColor_outside c π (root_not_mem_Ti c π hi), baseColor_root]
    exact hxZ.2

/-- Original successor steps inside T_i remain successor steps after shifting. -/
theorem step_preserved_inside (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i : ℕ} {x y : V}
    (h : LayerSets.InsideStep (R c π) (Ti c π i) x y) :
    ColorStep G (shiftedColor c π i) (finRotate 5) x y := by
  rcases h with ⟨hx, hy, hxy, hc⟩
  refine ⟨hxy, ?_⟩
  rw [shiftedColor_inside c π hy, shiftedColor_inside c π hx, hc]
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Original successor steps outside T_i remain unchanged. -/
theorem step_preserved_outside (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i : ℕ} {x y : V}
    (h : LayerSets.AvoidStep (R c π) (Ti c π i) x y) :
    ColorStep G (shiftedColor c π i) (finRotate 5) x y := by
  rcases h with ⟨hx, hy, hxy, hc⟩
  refine ⟨hxy, ?_⟩
  rw [shiftedColor_outside c π hy, shiftedColor_outside c π hx]
  exact hc

theorem reach_preserved_inside (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i : ℕ} {x y : V}
    (h : Relation.ReflTransGen (LayerSets.InsideStep (R c π) (Ti c π i)) x y) :
    Relation.ReflTransGen (ColorStep G (shiftedColor c π i) (finRotate 5)) x y :=
  (Relation.ReflTransGen.mono (fun _a _b hxy => step_preserved_inside c π hxy)) _ _ h

theorem reach_preserved_outside (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i : ℕ} {x y : V}
    (h : Relation.ReflTransGen (LayerSets.AvoidStep (R c π) (Ti c π i)) x y) :
    Relation.ReflTransGen (ColorStep G (shiftedColor c π i) (finRotate 5)) x y :=
  (Relation.ReflTransGen.mono (fun _a _b hxy => step_preserved_outside c π hxy)) _ _ h

theorem chain_preserved_inside (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i n : ℕ} {x y : V}
    (h : LayerSets.Chain (LayerSets.InsideStep (R c π) (Ti c π i)) x n y) :
    LayerSets.Chain (ColorStep G (shiftedColor c π i) (finRotate 5)) x n y :=
  h.mono (fun {_a _b} hxy => step_preserved_inside c π hxy)

theorem chain_preserved_outside (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (π : Equiv.Perm (Fin 5)) {i n : ℕ} {x y : V}
    (h : LayerSets.Chain (LayerSets.AvoidStep (R c π) (Ti c π i)) x n y) :
    LayerSets.Chain (ColorStep G (shiftedColor c π i) (finRotate 5)) x n y :=
  h.mono (fun {_a _b} hxy => step_preserved_outside c π hxy)

end TaskH.Five.LayerColoring


#print axioms TaskH.Five.LayerColoring.baseColor
#print axioms TaskH.Five.LayerColoring.baseColor_root
#print axioms TaskH.Five.LayerColoring.baseColor_outside
#print axioms TaskH.Five.LayerColoring.baseColor_adj_ne_outside
#print axioms TaskH.Five.LayerColoring.Z
#print axioms TaskH.Five.LayerColoring.baseColor_mono_iff
#print axioms TaskH.Five.LayerColoring.Z_nonempty
#print axioms TaskH.Five.LayerColoring.R
#print axioms TaskH.Five.LayerColoring.Ti
#print axioms TaskH.Five.LayerColoring.root_not_mem_Ti
#print axioms TaskH.Five.LayerColoring.shiftedColor
#print axioms TaskH.Five.LayerColoring.shiftedColor_inside
#print axioms TaskH.Five.LayerColoring.shiftedColor_outside
#print axioms TaskH.Five.LayerColoring.M
#print axioms TaskH.Five.LayerColoring.shifted_mono_cover
#print axioms TaskH.Five.LayerColoring.M_edge_mono
#print axioms TaskH.Five.LayerColoring.step_preserved_inside
#print axioms TaskH.Five.LayerColoring.step_preserved_outside
#print axioms TaskH.Five.LayerColoring.reach_preserved_inside
#print axioms TaskH.Five.LayerColoring.reach_preserved_outside
#print axioms TaskH.Five.LayerColoring.chain_preserved_inside
#print axioms TaskH.Five.LayerColoring.chain_preserved_outside
