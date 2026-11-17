import Research.TaskH.Seven.LayerColoring
import Research.TaskH.Seven.CycleFlux
import Research.TaskH.DirectedCycle

/-!
Transport the finite seven-color flux identity to genuine graph edges and
walks. Label color 6 at the root is kept distinct from order rank 7 there.
-/

universe u

namespace TaskH.Seven.LayerFlux

open SimpleGraph _root_.TaskH.Seven.LayerColoring _root_.TaskH.Seven.GoodCycles

variable {V : Type u} {G : SimpleGraph V} {v : V}

noncomputable def rootFlag (v x : V) : Bool := by
  classical
  exact decide (x = v)

noncomputable def shiftFlag (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (i : ℕ) (x : V) : Bool := by
  classical
  exact decide (x ∈ Ti c π i)

/-- The integer label before reducing the shifted color modulo seven. -/
noncomputable def integerLabel (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (i : ℕ) (x : V) : ℤ := by
  classical
  exact ((baseColor c π x).val : ℤ) - (if x ∈ Ti c π i then 1 else 0)

theorem shiftedColor_eq_shiftBit (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (i : ℕ) (x : V) :
    shiftedColor c π i x = shiftBit (baseColor c π x) (shiftFlag c π i x) := by
  classical
  by_cases hx : x ∈ Ti c π i <;> simp [shiftedColor, shiftBit, shiftFlag, hx]

theorem integerLabel_eq_flags (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (i : ℕ) (x : V) :
    integerLabel c π i x = ((baseColor c π x).val : ℤ) -
      (if shiftFlag c π i x then 1 else 0) := by
  classical
  by_cases hx : x ∈ Ti c π i <;> simp [integerLabel, shiftFlag, hx]

/-- The rank is seven at the root and the actual base-color rank elsewhere. -/
theorem orderColor_val_eq_flags (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (x : V) :
    (orderColor c π x).val = if rootFlag v x then 7 else (baseColor c π x).val := by
  classical
  by_cases hx : x = v
  · subst x
    rw [orderColor_base]
    simp [rootFlag]
  · rw [orderColor_outside c π x hx, baseColor_outside c π hx]
    simp [rootFlag, hx]

/-- Every genuine shifted successor edge satisfies the required integer flux. -/
theorem point_flow (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {i : ℕ} (hi : 1 ≤ i) {x y : V}
    (hstep : ColorStep G (shiftedColor c π i) (finRotate 7) x y) :
    integerLabel c π i y - integerLabel c π i x =
      1 - 7 * (if orderColor c π y < orderColor c π x then 1 else 0) := by
  classical
  have hxroot : rootFlag v x = true →
      baseColor c π x = 6 ∧ shiftFlag c π i x = false := by
    intro hr
    have hx : x = v := by simpa [rootFlag] using hr
    subst x
    exact ⟨baseColor_root c π, by simp [shiftFlag, root_not_mem_Ti c π hi]⟩
  have hyroot : rootFlag v y = true →
      baseColor c π y = 6 ∧ shiftFlag c π i y = false := by
    intro hr
    have hy : y = v := by simpa [rootFlag] using hr
    subst y
    exact ⟨baseColor_root c π, by simp [shiftFlag, root_not_mem_Ti c π hi]⟩
  have hnotboth : ¬ (rootFlag v x = true ∧ rootFlag v y = true) := by
    rintro ⟨hx, hy⟩
    have hxv : x = v := by simpa [rootFlag] using hx
    have hyv : y = v := by simpa [rootFlag] using hy
    exact hstep.1.ne (hxv.trans hyv.symm)
  have hnonroot : rootFlag v x = false ∧ rootFlag v y = false →
      baseColor c π x ≠ baseColor c π y := by
    rintro ⟨hx, hy⟩
    have hxv : x ≠ v := by simpa [rootFlag] using hx
    have hyv : y ≠ v := by simpa [rootFlag] using hy
    exact baseColor_adj_ne_outside c π hstep.1 hxv hyv
  have hsucc : shiftBit (baseColor c π y) (shiftFlag c π i y) =
      finRotate 7 (shiftBit (baseColor c π x) (shiftFlag c π i x)) := by
    have hs := hstep.2
    rw [shiftedColor_eq_shiftBit c π i y, shiftedColor_eq_shiftBit c π i x] at hs
    exact hs
  have hflow := finite_layer_flow (baseColor c π x) (baseColor c π y)
    (shiftFlag c π i x) (shiftFlag c π i y) (rootFlag v x) (rootFlag v y)
    hxroot hyroot hnotboth hnonroot hsucc
  rw [integerLabel_eq_flags c π i y, integerLabel_eq_flags c π i x]
  simpa only [Fin.lt_def, orderColor_val_eq_flags c π y,
    orderColor_val_eq_flags c π x] using hflow

/-- On every actual closed shifted-successor walk the integer increments telescope. -/
theorem follows_closed_length_eq_seven_descents
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (π : Equiv.Perm (Fin 7))
    {i : ℕ} (hi : 1 ≤ i) {x : V} (p : G.Walk x x)
    (hf : Follows p (shiftedColor c π i) (finRotate 7)) :
    p.length = 7 * rawDescents (orderColor c π) p := by
  apply closed_length_eq_seven_descents p (orderColor c π) (integerLabel c π i)
  intro d hd
  exact point_flow c π hi ⟨d.adj, hf d hd⟩

theorem follows_closed_length_dvd
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (π : Equiv.Perm (Fin 7))
    {i : ℕ} (hi : 1 ≤ i) {x : V} (p : G.Walk x x)
    (hf : Follows p (shiftedColor c π i) (finRotate 7)) : 7 ∣ p.length :=
  ⟨rawDescents (orderColor c π) p, follows_closed_length_eq_seven_descents c π hi p hf⟩

/-- A constructed genuine cycle is good in the original unshifted vertex order. -/
theorem follows_cycle_good [DecidableEq V]
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (π : Equiv.Perm (Fin 7))
    {i : ℕ} (hi : 1 ≤ i) {x : V} (p : G.Walk x x) (hp : p.IsCycle)
    (hf : Follows p (shiftedColor c π i) (finRotate 7)) :
    GoodCycleOrder c π p.edges.toFinset := by
  refine ⟨x, p, hp, p.coe_edges_toFinset.symm,
    follows_closed_length_dvd c π hi p hf, ?_⟩
  exact (follows_closed_length_eq_seven_descents c π hi p hf).ge

end TaskH.Seven.LayerFlux


#print axioms TaskH.Seven.LayerFlux.rootFlag
#print axioms TaskH.Seven.LayerFlux.shiftFlag
#print axioms TaskH.Seven.LayerFlux.integerLabel
#print axioms TaskH.Seven.LayerFlux.shiftedColor_eq_shiftBit
#print axioms TaskH.Seven.LayerFlux.integerLabel_eq_flags
#print axioms TaskH.Seven.LayerFlux.orderColor_val_eq_flags
#print axioms TaskH.Seven.LayerFlux.point_flow
#print axioms TaskH.Seven.LayerFlux.follows_closed_length_eq_seven_descents
#print axioms TaskH.Seven.LayerFlux.follows_closed_length_dvd
#print axioms TaskH.Seven.LayerFlux.follows_cycle_good
