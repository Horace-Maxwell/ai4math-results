import Research.Backfill.Paper7.SchwenkPunctureGraph

/-! Actual walks and actual vertex-deletion types for induction along a path.
No vertex or detached component is discarded except the explicitly deleted ones. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicSchwenk
open SimpleGraph BackfillPaper7.Challenge.Legacy.Algebra
open scoped Classical

/-- A walk avoiding u, viewed in the actual induced graph without u. -/
def punctureWalk {V : Type} {G : SimpleGraph V} {v w : V}
    (u : V) (p : G.Walk v w) (hu : u ∉ p.support) :
    (G.induce {x | x ≠ u}).Walk
      ⟨v, fun h => hu (h ▸ p.start_mem_support)⟩
      ⟨w, fun h => hu (h ▸ p.end_mem_support)⟩ :=
  p.induce {x | x ≠ u} (fun _ hx h => hu (h ▸ hx))
#print axioms Paper7UnicyclicSchwenk.punctureWalk

theorem punctureWalk_map {V : Type} {G : SimpleGraph V} {v w : V}
    (u : V) (p : G.Walk v w) (hu : u ∉ p.support) :
    (punctureWalk u p hu).map (Embedding.induce (G := G) {x | x ≠ u}).toHom = p := by
  simp only [punctureWalk, Walk.map_induce]
  rfl
#print axioms Paper7UnicyclicSchwenk.punctureWalk_map

theorem punctureWalk_length {V : Type} {G : SimpleGraph V} {v w : V}
    (u : V) (p : G.Walk v w) (hu : u ∉ p.support) :
    (punctureWalk u p hu).length = p.length := by
  exact (Walk.length_map (Embedding.induce (G := G) {x | x ≠ u}).toHom
    (punctureWalk u p hu)).symm.trans
      (congrArg (fun q : G.Walk v w => q.length) (punctureWalk_map u p hu))
#print axioms Paper7UnicyclicSchwenk.punctureWalk_length

theorem punctureWalk_isPath {V : Type} {G : SimpleGraph V} {v w : V}
    (u : V) (p : G.Walk v w) (hu : u ∉ p.support) (hp : p.IsPath) :
    (punctureWalk u p hu).IsPath := by
  have hm : ((punctureWalk u p hu).map
      (Embedding.induce (G := G) {x | x ≠ u}).toHom).IsPath := by
    rw [punctureWalk_map]
    exact hp
  exact hm.of_map
#print axioms Paper7UnicyclicSchwenk.punctureWalk_isPath

theorem punctureWalk_mem_support {V : Type} {G : SimpleGraph V} {v w : V}
    (u : V) (p : G.Walk v w) (hu : u ∉ p.support) (x : {x : V // x ≠ u}) :
    x ∈ (punctureWalk u p hu).support ↔ x.val ∈ p.support := by
  have hm : (punctureWalk u p hu).support.map Subtype.val = p.support :=
    (Walk.support_map (Embedding.induce (G := G) {x | x ≠ u}).toHom
      (punctureWalk u p hu)).symm.trans
        (congrArg (fun q : G.Walk v w => q.support) (punctureWalk_map u p hu))
  have hmemb := congrArg (fun l : List V => x.val ∈ l) hm
  constructor
  · intro hx
    exact hmemb ▸ List.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp (hmemb.symm ▸ hx)
    have hxy : y = x := Subtype.ext hyx
    exact hxy ▸ hy
#print axioms Paper7UnicyclicSchwenk.punctureWalk_mem_support

/-- Flatten precisely the two successive vertex-deletion subtypes. -/
def pathDeletionEquiv {V : Type} {G : SimpleGraph V} {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) (hu : u ∉ p.support) :
    {z : {x : V // x ≠ u} // z ∉ (punctureWalk u p hu).support} ≃
      {z : V // z ∉ (Walk.cons h p).support} where
  toFun z := ⟨z.val.val, by
    intro hz
    have hz' : z.val.val = u ∨ z.val.val ∈ p.support := by
      simpa only [Walk.support_cons, List.mem_cons] using hz
    rcases hz' with hzu | hzp
    · exact z.val.property hzu
    · exact z.property ((punctureWalk_mem_support u p hu z.val).mpr hzp)⟩
  invFun z := by
    have hzu : z.val ≠ u := by
      intro hz
      apply z.property
      simp only [Walk.support_cons, List.mem_cons]
      exact Or.inl hz
    refine ⟨⟨z.val, hzu⟩, ?_⟩
    intro hz
    apply z.property
    simp only [Walk.support_cons, List.mem_cons]
    exact Or.inr ((punctureWalk_mem_support u p hu ⟨z.val, hzu⟩).mp hz)
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
#print axioms Paper7UnicyclicSchwenk.pathDeletionEquiv

/-- The induced tail deletion and the full original path deletion have the
same actual graph polynomial, even when no vertices remain. -/
theorem puncture_path_complement_phi {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) (hu : u ∉ p.support) :
    graphPhi (deleteVertices (G.induce {x | x ≠ u})
      {z | z ∈ (punctureWalk u p hu).support}) =
      graphPhi (deleteVertices G {z | z ∈ (Walk.cons h p).support}) := by
  apply graphPhi_equiv _ _ (pathDeletionEquiv h p hu)
  intro i j
  rfl
#print axioms Paper7UnicyclicSchwenk.puncture_path_complement_phi

end Paper7UnicyclicSchwenk
