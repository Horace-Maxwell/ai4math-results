import Research.TaskH.FourColorPerms
import Research.TaskH.CycleOrientation
import Research.TaskH.Basics

/-!
Critical-edge recolouring produces actual four-cycles under the short-cycle
conclusion of the equality argument. ShortFourCycles is an internal result
to be derived from the original equality hypotheses, not a new hypothesis
in the frozen Question 2 or CaseFour statements.
-/

set_option autoImplicit false

universe u v

namespace TaskH

open Challenge SimpleGraph

variable {V : Type u} {α : Type v} {G : SimpleGraph V}

def ShortFourCycles (G : SimpleGraph V) : Prop :=
  ∀ {x : V} (p : G.Walk x x), p.IsCycle → 4 ∣ p.length → p.length = 4

theorem fourColorCycle_no_fixed (i : Fin 3) (a : Fin 4) :
    fourColorCycle i a ≠ a := by
  intro h
  exact fourColorCycle_no_two_step i a ((congrArg (fourColorCycle i) h).trans h)

/-- The reverse reachability argument keeps the very same deleted-edge graph
and coloring; no transport of the coloring through a graph equality is used. -/
theorem critical_edge_reachable_from_right (h : IsCriticalPlus 4 G) {x y : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 4)) (σ : Equiv.Perm (Fin 4))
    (hchange : σ (c y) ≠ c y) :
    Relation.ReflTransGen (ColorStep (G.deleteEdges {s(x, y)}) c σ) y x := by
  classical
  by_contra hnot
  let S : Set V := {z | Relation.ReflTransGen
    (ColorStep (G.deleteEdges {s(x, y)}) c σ) y z}
  have hclosed : ∀ {a b : V}, a ∈ S →
      ColorStep (G.deleteEdges {s(x, y)}) c σ a b → b ∈ S := by
    intro a b ha hab
    exact ha.tail hab
  let d := recolorClosed c σ S hclosed
  have hd : d x = d y := deletedEdge_coloring_endpoints h d
  have hy : y ∈ S := Relation.ReflTransGen.refl
  have hx : x ∉ S := hnot
  have hxv : d x = c x := by
    simpa only [ite_eq_right hx] using (recolorClosed_apply c σ S hclosed x)
  have hyv : d y = σ (c y) := by
    simpa only [ite_eq_left hy] using (recolorClosed_apply c σ S hclosed y)
  have he : σ (c y) = c x := hyv.symm.trans (hd.symm.trans hxv)
  exact hchange (he.trans (deletedEdge_coloring_endpoints h c))

/-- Every prefix of a following walk has the expected color-permutation power. -/
theorem follows_getVert {x y : V} (p : G.Walk x y) (c : V → α)
    (σ : Equiv.Perm α) (hf : Follows p c σ) :
    ∀ n : ℕ, n ≤ p.length → c (p.getVert n) = (σ ^ n) (c x) := by
  revert hf
  induction p with
  | nil =>
    intro _ n hn
    have hn0 : n = 0 := by simpa only [Walk.length_nil, Nat.le_zero] using hn
    subst n
    rfl
  | @cons x y z hxy p ih =>
    intro hf n hn
    have hs := (follows_cons hxy p c σ).mp hf
    cases n with
    | zero => rfl
    | succ n =>
      have hn' : n ≤ p.length := by
        simpa only [Walk.length_cons, Nat.add_le_add_iff_right] using hn
      calc
        c ((Walk.cons hxy p).getVert (n + 1)) = c (p.getVert n) := rfl
        _ = (σ ^ n) (c y) := ih hs.2 n hn'
        _ = (σ ^ (n + 1)) (c x) := by
          rw [hs.1, pow_succ]
          rfl

/-- A four-step following closed walk visits its base color only at its base vertex. -/
theorem follows_four_cycle_avoids_same_color {x y : V} (p : G.Walk x x)
    (c : V → Fin 4) (i : Fin 3) (hf : Follows p c (fourColorCycle i))
    (hl : p.length = 4) (he : c y = c x) (hne : x ≠ y) : y ∉ p.support := by
  intro hy
  obtain ⟨n, hn, hny⟩ := List.mem_iff_getElem.mp hy
  have hn' : n ≤ p.length := by
    rw [Walk.length_support] at hn
    omega
  have hv : p.getVert n = y := (p.getVert_eq_support_getElem hn').trans hny
  have hc : (fourColorCycle i ^ n) (c x) = c x :=
    (follows_getVert p c (fourColorCycle i) hf n hn').symm.trans
      ((congrArg c hv).trans he)
  have hd : 4 ∣ n := (fourColorCycle_pow_fixed_iff i (c x) n).mp hc
  have hn04 : n = 0 ∨ n = 4 := by
    obtain ⟨t, ht⟩ := hd
    omega
  rcases hn04 with hn0 | hn4
  · exact hne (by simpa only [hn0, Walk.getVert_zero] using hv)
  · have h4 : p.getVert 4 = x := by simpa only [hl] using p.getVert_length
    exact hne (h4.symm.trans (hn4 ▸ hv))

/-- For each of the three four-color cyclic orders, an actual cycle through x
avoids the other endpoint y of the deleted critical edge. -/
theorem critical_edge_four_cycle (h : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    {x y : V} (hxy : G.Adj x y)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 4)) (i : Fin 3) :
    ∃ q : G.Walk x x, q.IsCycle ∧ q.length = 4 ∧
      Follows q c (fourColorCycle i) ∧ y ∉ q.support := by
  have hmono : ColorStep (G.deleteEdges {s(x, y)}) c (fourColorCycle i) ≤
      ColorStep G c (fourColorCycle i) := by
    intro a b hab
    exact ⟨(SimpleGraph.deleteEdges_adj.mp hab.1).1, hab.2⟩
  have hrxy := Relation.ReflTransGen.mono hmono x y
    (critical_edge_reachable h c (fourColorCycle i) (fourColorCycle_no_fixed i (c x)))
  have hryx := Relation.ReflTransGen.mono hmono y x
    (critical_edge_reachable_from_right h c (fourColorCycle i)
      (fourColorCycle_no_fixed i (c y)))
  obtain ⟨p, hp⟩ := reach_exists_follows_walk c (fourColorCycle i) hrxy
  obtain ⟨r, hr⟩ := reach_exists_follows_walk c (fourColorCycle i) hryx
  have hpos : 0 < p.length := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hxy.ne)
  have hnon : p.append r ≠ .nil := by
    intro heq
    have hz := congrArg Walk.length heq
    simp only [Walk.length_append, Walk.length_nil] at hz
    omega
  have hf := (follows_append p r c (fourColorCycle i)).mpr ⟨hp, hr⟩
  obtain ⟨q, hq, hqf⟩ := follows_closed_exists_cycle (p.append r) hnon c
    (fourColorCycle i) hf (fourColorCycle_no_two_step i (c x))
  have hlen := hs q hq (follows_fourColorCycle_length_dvd q c i hqf)
  refine ⟨q, hq, hlen, hqf, ?_⟩
  exact follows_four_cycle_avoids_same_color q c i hqf hlen
    (deletedEdge_coloring_endpoints h c).symm hxy.ne

def CycleContains (s : Finset (Sym2 V)) (x : V) : Prop :=
  ∃ e ∈ s, x ∈ e

def modCyclesThroughAvoid (k : ℕ) (G : SimpleGraph V) (x y : V) :
    Set (Finset (Sym2 V)) :=
  {s | s ∈ ModCycleEdgeSets k G ∧ CycleContains s x ∧ ¬ CycleContains s y}

theorem cycleContains_edges_toFinset_iff [DecidableEq V] {a b : V}
    (p : G.Walk a b) (hp : ¬ p.Nil) (x : V) :
    CycleContains p.edges.toFinset x ↔ x ∈ p.support := by
  rw [Walk.mem_support_iff_exists_mem_edges_of_not_nil hp]
  simp only [CycleContains, List.mem_toFinset]

theorem mem_modCyclesThroughAvoid_of_cycle [DecidableEq V] {x y : V}
    {p : G.Walk x x} (hp : p.IsCycle) (hl : p.length = 4) (hy : y ∉ p.support) :
    p.edges.toFinset ∈ modCyclesThroughAvoid 4 G x y := by
  refine ⟨(Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr ?_, ?_, ?_⟩
  · simpa only [hl] using (dvd_refl 4)
  · exact (cycleContains_edges_toFinset_iff p hp.not_nil x).mpr p.start_mem_support
  · intro h
    exact hy ((cycleContains_edges_toFinset_iff p hp.not_nil y).mp h)

end TaskH

#print axioms TaskH.critical_edge_reachable_from_right
#print axioms TaskH.follows_getVert
#print axioms TaskH.critical_edge_four_cycle
#print axioms TaskH.cycleContains_edges_toFinset_iff
#print axioms TaskH.mem_modCyclesThroughAvoid_of_cycle
