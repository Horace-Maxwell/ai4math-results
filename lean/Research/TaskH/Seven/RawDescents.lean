import Research.TaskH.Basics
import Research.TaskH.ColorWords

set_option autoImplicit false

universe u

namespace TaskH.Seven.GoodCycles

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {v : V}

/-- Actual edge descents, with no chosen starting point retained. -/
def rawDescents {x y : V} (r : V → Fin 8) (p : G.Walk x y) : ℕ :=
  (p.darts.filter fun d => decide (r d.snd < r d.fst)).length

theorem rawDescents_nil (r : V → Fin 8) (x : V) :
    rawDescents r (.nil : G.Walk x x) = 0 := rfl

theorem rawDescents_cons {x y z : V} (r : V → Fin 8)
    (hxy : G.Adj x y) (p : G.Walk y z) :
    rawDescents r (.cons hxy p) = (if r y < r x then 1 else 0) + rawDescents r p := by
  by_cases hr : r y < r x
  · simp [rawDescents, Walk.darts_cons, hr, Nat.add_comm]
  · simp [rawDescents, Walk.darts_cons, hr]

theorem rawDescents_append {x y z : V} (r : V → Fin 8)
    (p : G.Walk x y) (q : G.Walk y z) :
    rawDescents r (p.append q) = rawDescents r p + rawDescents r q := by
  simp only [rawDescents, Walk.darts_append, List.filter_append, List.length_append]

theorem rawDescents_rotate [DecidableEq V] {x : V} (r : V → Fin 8) (p : G.Walk x x)
    (y : V) (hy : y ∈ p.support) : rawDescents r (p.rotate y hy) = rawDescents r p := by
  exact ((p.rotate_darts y hy).perm.filter _).length_eq

theorem rawDescents_rotate_reverse [DecidableEq V] {x : V} (r : V → Fin 8) (p : G.Walk x x)
    (y : V) (hy : y ∈ p.support) :
    rawDescents r (p.rotate y hy).reverse = rawDescents r p.reverse := by
  unfold rawDescents
  simp only [Walk.darts_reverse, List.filter_reverse, List.length_reverse]
  exact (((p.rotate_darts y hy).perm.map Dart.symm).filter _).length_eq

/-- The deleted vertex is strictly after all seven color classes. -/
noncomputable def orderColor (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (x : V) : Fin 8 := by
  classical
  exact if hx : x = v then 7 else (π (c ⟨x, hx⟩)).castSucc

theorem orderColor_base (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) : orderColor c π v = 7 := by
  classical
  simp [orderColor]

theorem orderColor_outside (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (x : V) (hx : x ≠ v) :
    orderColor c π x = (π (c ⟨x, hx⟩)).castSucc := by
  classical
  simp [orderColor, hx]

theorem orderColor_adj_ne (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {x y : V} (hxy : G.Adj x y) :
    orderColor c π x ≠ orderColor c π y := by
  classical
  by_cases hx : x = v
  · subst x
    have hy : y ≠ v := hxy.ne.symm
    rw [orderColor_base, orderColor_outside c π y hy]
    intro heq
    have hv := congrArg Fin.val heq
    change (7 : ℕ) = (π (c ⟨y, hy⟩)).val at hv
    have hb := (π (c ⟨y, hy⟩)).isLt
    omega
  · by_cases hy : y = v
    · subst y
      rw [orderColor_outside c π x hx, orderColor_base]
      intro heq
      have hv := congrArg Fin.val heq
      change (π (c ⟨x, hx⟩)).val = (7 : ℕ) at hv
      have hb := (π (c ⟨x, hx⟩)).isLt
      omega
    · rw [orderColor_outside c π x hx, orderColor_outside c π y hy]
      intro heq
      have hval := congrArg Fin.val heq
      have hc : c ⟨x, hx⟩ ≠ c ⟨y, hy⟩ := c.valid hxy
      exact hc (π.injective (Fin.ext hval))

/-- This is the paper's good-cycle predicate on the actual unoriented edge
set. A witness may use either direction or any starting point. -/
noncomputable def GoodCycleOrder (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (s : Finset (Sym2 V)) : Prop :=
  ∃ (x : V) (p : G.Walk x x), p.IsCycle ∧ p.edgeSet = (s : Set (Sym2 V)) ∧
    7 ∣ p.length ∧ 7 * rawDescents (orderColor c π) p ≤ p.length

#print axioms rawDescents
#print axioms rawDescents_nil
#print axioms rawDescents_cons
#print axioms rawDescents_append
#print axioms rawDescents_rotate
#print axioms rawDescents_rotate_reverse
#print axioms orderColor
#print axioms orderColor_base
#print axioms orderColor_outside
#print axioms orderColor_adj_ne
#print axioms GoodCycleOrder

end TaskH.Seven.GoodCycles
