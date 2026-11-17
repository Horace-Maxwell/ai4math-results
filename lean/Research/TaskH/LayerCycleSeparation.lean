import Research.TaskH.NestedShift
import Research.TaskH.CycleOrientation

set_option autoImplicit false

universe u

namespace TaskH.GoodCycles

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

theorem follows_iff_of_darts_perm {α : Type*} {x y z w : V}
    (p : G.Walk x y) (q : G.Walk z w) (h : p.darts.Perm q.darts)
    (c : V → α) (σ : Equiv.Perm α) : Follows p c σ ↔ Follows q c σ := by
  constructor
  · intro hp d hd
    exact hp d (h.mem_iff.mpr hd)
  · intro hq d hd
    exact hq d (h.mem_iff.mp hd)

theorem follows_rotate_iff [DecidableEq V] {α : Type*} {x : V}
    (p : G.Walk x x) (y : V) (hy : y ∈ p.support)
    (c : V → α) (σ : Equiv.Perm α) :
    Follows (p.rotate y hy) c σ ↔ Follows p c σ :=
  follows_iff_of_darts_perm _ _ (p.rotate_darts y hy).perm c σ

theorem follows_rotate_reverse_iff [DecidableEq V] {α : Type*} {x : V}
    (p : G.Walk x x) (y : V) (hy : y ∈ p.support)
    (c : V → α) (σ : Equiv.Perm α) :
    Follows (p.rotate y hy).reverse c σ ↔ Follows p.reverse c σ := by
  apply follows_iff_of_darts_perm
  simp only [Walk.darts_reverse]
  exact (List.reverse_perm _).trans
    (((p.rotate_darts y hy).perm.map Dart.symm).trans (List.reverse_perm _).symm)

/-- Cycles obtained at different boundaries of nested layers have different
unoriented edge sets. All hypotheses refer to actual cycles and color steps. -/
theorem layer_cycle_edges_ne_of_lt [DecidableEq V]
    (c : V → Fin 4) (T : ℕ → Set V)
    (hanti : ∀ {i j : ℕ}, i ≤ j → T j ⊆ T i)
    (t : Fin 5 → V) (p : ∀ i : Fin 5, G.Walk (t i) (t i))
    (hp : ∀ i, (p i).IsCycle)
    (hf : ∀ i, Follows (p i)
      (fun z => shiftBit (c z) (decide (z ∈ T (i.val + 1)))) (finRotate 4))
    (ht : ∀ i, t i ∈ T i.val ∧ t i ∉ T (i.val + 1))
    (i j : Fin 5) (hij : i.val < j.val) :
    (p i).edges.toFinset ≠ (p j).edges.toFinset := by
  intro heq
  let si : V → Bool := fun z => decide (z ∈ T (i.val + 1))
  let sj : V → Bool := fun z => decide (z ∈ T (j.val + 1))
  have hsub : ∀ z, sj z = true → si z = true := by
    intro z hz
    have hzmem : z ∈ T (j.val + 1) := by simpa only [sj, decide_eq_true_eq] using hz
    have hm : z ∈ T (i.val + 1) := hanti (by omega) hzmem
    simpa only [si, decide_eq_true_eq] using hm
  have hfi : Follows (p i) (fun z => shiftBit (c z) (si z)) (finRotate 4) := hf i
  have htji : t j ∈ T (i.val + 1) := hanti (by omega) (ht j).1
  have htii := (ht i).2
  have htjj := (ht j).2
  obtain ⟨hmem, hq | hq⟩ :=
    CycleOrientation.cycle_eq_rotate_or_reverse_of_toFinset_eq (hp i) (hp j) heq
  · have hfjrot : Follows ((p i).rotate (t j) hmem)
        (fun z => shiftBit (c z) (sj z)) (finRotate 4) := by
      rw [← hq]
      exact hf j
    have hfj := (follows_rotate_iff (p i) (t j) hmem
      (fun z => shiftBit (c z) (sj z)) (finRotate 4)).mp hfjrot
    have hm := nested_mark_constant (p i) c si sj hsub hfi hfj (t j) hmem
    simp [si, sj, htji, htii, htjj] at hm
  · have hfjrot : Follows ((p i).rotate (t j) hmem).reverse
        (fun z => shiftBit (c z) (sj z)) (finRotate 4) := by
      rw [← hq]
      exact hf j
    have hfj := (follows_rotate_reverse_iff (p i) (t j) hmem
      (fun z => shiftBit (c z) (sj z)) (finRotate 4)).mp hfjrot
    exact nested_opposite_impossible (p i) (by have h := (hp i).three_le_length; omega)
      c si sj hsub hfi hfj

theorem layer_cycle_edgeSets_injective [DecidableEq V]
    (c : V → Fin 4) (T : ℕ → Set V)
    (hanti : ∀ {i j : ℕ}, i ≤ j → T j ⊆ T i)
    (t : Fin 5 → V) (p : ∀ i : Fin 5, G.Walk (t i) (t i))
    (hp : ∀ i, (p i).IsCycle)
    (hf : ∀ i, Follows (p i)
      (fun z => shiftBit (c z) (decide (z ∈ T (i.val + 1)))) (finRotate 4))
    (ht : ∀ i, t i ∈ T i.val ∧ t i ∉ T (i.val + 1)) :
    Function.Injective (fun i => (p i).edges.toFinset) := by
  intro i j heq
  by_contra hne
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h | h
  · exact layer_cycle_edges_ne_of_lt c T hanti t p hp hf ht i j h heq
  · exact layer_cycle_edges_ne_of_lt c T hanti t p hp hf ht j i h heq.symm

#print axioms follows_rotate_iff
#print axioms layer_cycle_edges_ne_of_lt
#print axioms layer_cycle_edgeSets_injective

end TaskH.GoodCycles
