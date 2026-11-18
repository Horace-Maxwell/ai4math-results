import Mathlib

/-! Actual spanning cuts: the vertex carrier is exactly the original V. -/
set_option autoImplicit false
universe u
namespace TaskH.Bai
open SimpleGraph Finset
variable {V : Type u}

/-- All and only original edges whose Boolean colors differ. -/
def spanningCut (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ c a ≠ c b
  symm.symm _a _b h := ⟨h.1.symm, Ne.symm h.2⟩
  loopless.irrefl _a h := h.2 rfl

instance spanningCutDecidable (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    DecidableRel (spanningCut G c).Adj :=
  inferInstanceAs (DecidableRel fun a b => G.Adj a b ∧ c a ≠ c b)

/-- Flip the actual colors on an arbitrary actual set of original vertices. -/
noncomputable def cutFlip (c : V → Bool) (S : Set V) : V → Bool := by
  classical
  exact fun v => if v ∈ S then !(c v) else c v

theorem spanningCut_le (G : SimpleGraph V) (c : V → Bool) : spanningCut G c ≤ G :=
  fun _ _ h => h.1

theorem spanningCut_bipartite (G : SimpleGraph V) (c : V → Bool) :
    (spanningCut G c).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if c v then (1 : Fin 2) else 0) ?_⟩
  intro a b hab
  have hne : c a ≠ c b := hab.2
  cases hca : c a <;> cases hcb : c b <;> simp_all

/-- Flipping one vertex changes no edge not incident with that vertex. -/
theorem singleton_flip_delete_incidence (G : SimpleGraph V) (c : V → Bool) (v : V) :
    (spanningCut G (cutFlip c {v})).deleteIncidenceSet v =
      (spanningCut G c).deleteIncidenceSet v := by
  classical
  ext a b
  by_cases ha : a = v
  · subst a
    simp [SimpleGraph.deleteIncidenceSet_adj]
  · by_cases hb : b = v
    · subst b
      simp [SimpleGraph.deleteIncidenceSet_adj]
    · simp [SimpleGraph.deleteIncidenceSet_adj, spanningCut, cutFlip, ha, hb]

/-- The flipped neighbors of v are exactly its original noncrossing neighbors. -/
theorem singleton_flip_neighborFinset (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (c : V → Bool) (v : V) :
    (spanningCut G (cutFlip c {v})).neighborFinset v =
      G.neighborFinset v \ (spanningCut G c).neighborFinset v := by
  classical
  ext w
  rw [Finset.mem_sdiff]
  rw [(spanningCut G (cutFlip c {v})).mem_neighborFinset v w,
    G.mem_neighborFinset v w, (spanningCut G c).mem_neighborFinset v w]
  change (G.Adj v w ∧ cutFlip c {v} v ≠ cutFlip c {v} w) ↔
    (G.Adj v w ∧ ¬(G.Adj v w ∧ c v ≠ c w))
  by_cases hw : w = v
  · subst w
    simp only [G.irrefl, false_and, iff_self]
  · have hvflip : cutFlip c {v} v = !(c v) := by
      unfold cutFlip
      exact ite_eq_left (Set.mem_singleton v)
    have hwflip : cutFlip c {v} w = c w := by
      unfold cutFlip
      exact ite_eq_right ((Set.mem_singleton_iff).not.mpr hw)
    rw [hvflip, hwflip]
    cases hcv : c v <;> cases hcw : c w <;> simp_all

/-- If a set is closed across actual cut edges, its flip preserves every cut edge. -/
theorem cut_flip_le_of_edge_closed (G : SimpleGraph V) (c : V → Bool) (S : Set V)
    (hclosed : ∀ ⦃a b : V⦄, (spanningCut G c).Adj a b → (a ∈ S ↔ b ∈ S)) :
    spanningCut G c ≤ spanningCut G (cutFlip c S) := by
  classical
  intro a b hab
  refine ⟨hab.1, ?_⟩
  have hne : c a ≠ c b := hab.2
  have hs := hclosed hab
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
    cases hca : c a <;> cases hcb : c b <;> simp_all [cutFlip]

/-- A genuine original boundary edge becomes a new cut edge after this flip. -/
theorem cut_flip_adds_boundary_edge (G : SimpleGraph V) (c : V → Bool) (S : Set V)
    {a b : V} (ha : a ∈ S) (hb : b ∉ S) (hab : G.Adj a b)
    (hnot : ¬(spanningCut G c).Adj a b) :
    (spanningCut G (cutFlip c S)).Adj a b := by
  classical
  have heq : c a = c b := by
    by_contra hne
    exact hnot ⟨hab, hne⟩
  refine ⟨hab, ?_⟩
  cases hca : c a <;> cases hcb : c b <;> simp_all [cutFlip]

/-- A real walk leaving an actual set contains a real boundary edge. -/
theorem cut_walk_crossing (G : SimpleGraph V) (S : Set V)
    {a b : V} (p : G.Walk a b) : a ∈ S → b ∉ S →
    ∃ x ∈ S, ∃ y, y ∉ S ∧ G.Adj x y := by
  classical
  induction p with
  | nil =>
    intro ha hb
    exact False.elim (hb ha)
  | @cons a x b hax p ih =>
    intro ha hb
    by_cases hx : x ∈ S
    · exact ih hx hb
    · exact ⟨a, ha, x, hx, hax⟩

#print axioms spanningCut
#print axioms spanningCutDecidable
#print axioms cutFlip
#print axioms spanningCut_le
#print axioms spanningCut_bipartite
#print axioms singleton_flip_delete_incidence
#print axioms singleton_flip_neighborFinset
#print axioms cut_flip_le_of_edge_closed
#print axioms cut_flip_adds_boundary_edge
#print axioms cut_walk_crossing
end TaskH.Bai
