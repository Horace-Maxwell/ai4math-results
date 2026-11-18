import Research.TaskH.General.LayerColoring
import Research.TaskH.General.CycleFlux
import Research.TaskH.DirectedCycle

/-!
Transport the symbolic arbitrary-k flux identity to genuine graph edges and
walks. Root label k-1 in Fin k is kept distinct from vertex-order rank k in Fin (k+1).
-/

universe u

namespace TaskH.General.LayerFlux

open SimpleGraph _root_.TaskH.General.LayerColoring _root_.TaskH.General.GoodCycles

variable {V : Type u} {G : SimpleGraph V} {v : V} {k : ℕ} (hk : 3 ≤ k)

noncomputable def rootFlag (v x : V) : Bool := by
  classical
  exact decide (x = v)

noncomputable def shiftFlag (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) (i : ℕ) (x : V) : Bool := by
  classical
  exact decide (x ∈ Ti hk c π i)

/-- The integer label before reducing the shifted color modulo k. -/
noncomputable def integerLabel (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) (i : ℕ) (x : V) : ℤ := by
  classical
  exact ((baseColor hk c π x).val : ℤ) - (if x ∈ Ti hk c π i then 1 else 0)

theorem shiftedColor_eq_shiftBit (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) (i : ℕ) (x : V) :
    shiftedColor hk c π i x = shiftBit (baseColor hk c π x) (shiftFlag hk c π i x) := by
  classical
  by_cases hx : x ∈ Ti hk c π i <;> simp [shiftedColor, shiftBit, shiftFlag, hx]

theorem integerLabel_eq_flags (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) (i : ℕ) (x : V) :
    integerLabel hk c π i x = ((baseColor hk c π x).val : ℤ) -
      (if shiftFlag hk c π i x then 1 else 0) := by
  classical
  by_cases hx : x ∈ Ti hk c π i <;> simp [integerLabel, shiftFlag, hx]

/-- The rank is k at the root and the actual base-color rank elsewhere. -/
theorem orderColor_val_eq_flags (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) (x : V) :
    (orderColor c π x).val = if rootFlag v x then k else (baseColor hk c π x).val := by
  classical
  by_cases hx : x = v
  · subst x
    rw [orderColor_base]
    simp [rootFlag]
  · rw [orderColor_outside c π x hx, baseColor_outside hk c π hx]
    simp [rootFlag, hx]

/-- Every genuine shifted successor edge satisfies the required integer flux. -/
theorem point_flow (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)) {i : ℕ} (hi : 1 ≤ i) {x y : V}
    (hstep : ColorStep G (shiftedColor hk c π i) (finRotate k) x y) :
    integerLabel hk c π i y - integerLabel hk c π i x =
      1 - (k : ℤ) * (if orderColor c π y < orderColor c π x then 1 else 0) := by
  classical
  have hxroot : rootFlag v x = true →
      (baseColor hk c π x).val + 1 = k ∧ shiftFlag hk c π i x = false := by
    intro hr
    have hx : x = v := by simpa [rootFlag] using hr
    subst x
    refine ⟨?_, by simp [shiftFlag, root_not_mem_Ti hk c π hi]⟩
    rw [baseColor_root]
    change k - 1 + 1 = k
    omega
  have hyroot : rootFlag v y = true →
      (baseColor hk c π y).val + 1 = k ∧ shiftFlag hk c π i y = false := by
    intro hr
    have hy : y = v := by simpa [rootFlag] using hr
    subst y
    refine ⟨?_, by simp [shiftFlag, root_not_mem_Ti hk c π hi]⟩
    rw [baseColor_root]
    change k - 1 + 1 = k
    omega
  have hnotboth : ¬ (rootFlag v x = true ∧ rootFlag v y = true) := by
    rintro ⟨hx, hy⟩
    have hxv : x = v := by simpa [rootFlag] using hx
    have hyv : y = v := by simpa [rootFlag] using hy
    exact hstep.1.ne (hxv.trans hyv.symm)
  have hnonroot : rootFlag v x = false ∧ rootFlag v y = false →
      baseColor hk c π x ≠ baseColor hk c π y := by
    rintro ⟨hx, hy⟩
    have hxv : x ≠ v := by simpa [rootFlag] using hx
    have hyv : y ≠ v := by simpa [rootFlag] using hy
    exact baseColor_adj_ne_outside hk c π hstep.1 hxv hyv
  have hsucc : shiftBit (baseColor hk c π y) (shiftFlag hk c π i y) =
      finRotate k (shiftBit (baseColor hk c π x) (shiftFlag hk c π i x)) := by
    have hs := hstep.2
    rw [shiftedColor_eq_shiftBit hk c π i y, shiftedColor_eq_shiftBit hk c π i x] at hs
    exact hs
  have hflow := layer_flow hk (baseColor hk c π x) (baseColor hk c π y)
    (shiftFlag hk c π i x) (shiftFlag hk c π i y) (rootFlag v x) (rootFlag v y)
    hxroot hyroot hnotboth hnonroot hsucc
  rw [integerLabel_eq_flags hk c π i y, integerLabel_eq_flags hk c π i x]
  simpa only [Fin.lt_def, orderColor_val_eq_flags hk c π y,
    orderColor_val_eq_flags hk c π x] using hflow

/-- On every actual closed shifted-successor walk the integer increments telescope. -/
theorem follows_closed_length_eq_k_descents
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (π : Equiv.Perm (Fin k))
    {i : ℕ} (hi : 1 ≤ i) {x : V} (p : G.Walk x x)
    (hf : Follows p (shiftedColor hk c π i) (finRotate k)) :
    p.length = k * rawDescents (orderColor c π) p := by
  apply closed_length_eq_k_descents p (orderColor c π) (integerLabel hk c π i)
  intro d hd
  exact point_flow hk c π hi ⟨d.adj, hf d hd⟩

theorem follows_closed_length_dvd
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (π : Equiv.Perm (Fin k))
    {i : ℕ} (hi : 1 ≤ i) {x : V} (p : G.Walk x x)
    (hf : Follows p (shiftedColor hk c π i) (finRotate k)) : k ∣ p.length :=
  ⟨rawDescents (orderColor c π) p, follows_closed_length_eq_k_descents hk c π hi p hf⟩

/-- A constructed genuine cycle is good in the original unshifted vertex order. -/
theorem follows_cycle_good [DecidableEq V]
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (π : Equiv.Perm (Fin k))
    {i : ℕ} (hi : 1 ≤ i) {x : V} (p : G.Walk x x) (hp : p.IsCycle)
    (hf : Follows p (shiftedColor hk c π i) (finRotate k)) :
    GoodCycleOrder c π p.edges.toFinset := by
  refine ⟨x, p, hp, p.coe_edges_toFinset.symm,
    follows_closed_length_dvd hk c π hi p hf, ?_⟩
  exact (follows_closed_length_eq_k_descents hk c π hi p hf).ge

end TaskH.General.LayerFlux


#print axioms TaskH.General.LayerFlux.rootFlag
#print axioms TaskH.General.LayerFlux.shiftFlag
#print axioms TaskH.General.LayerFlux.integerLabel
#print axioms TaskH.General.LayerFlux.shiftedColor_eq_shiftBit
#print axioms TaskH.General.LayerFlux.integerLabel_eq_flags
#print axioms TaskH.General.LayerFlux.orderColor_val_eq_flags
#print axioms TaskH.General.LayerFlux.point_flow
#print axioms TaskH.General.LayerFlux.follows_closed_length_eq_k_descents
#print axioms TaskH.General.LayerFlux.follows_closed_length_dvd
#print axioms TaskH.General.LayerFlux.follows_cycle_good
