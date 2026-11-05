import Research.Backfill.Paper7.TreePathInstances

/-! Full path cofactor formula, proved for every finite acyclic graph by
induction on the actual supplied path length. No cofactor assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicSchwenk
open SimpleGraph BackfillPaper7.Challenge.Legacy.Algebra
open scoped Classical

/-- The induction changes the actual vertex type to a deletion subtype, so
all finite vertex types and acyclic graphs are generalized in the induction. -/
theorem acyclic_path_cofactor_aux (n : ℕ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.IsAcyclic → ∀ (u v : V) (p : G.Walk u v),
      p.IsPath → p.length = n →
      (Matrix.charmatrix (G.adjMatrix ℤ)).adjugate v u =
        graphPhi (deleteVertices G {z | z ∈ p.support}) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G _ hG u v p hp hn
    cases p with
    | nil =>
      let e : {z : V // z ∉ ({u} : Set V)} ≃
          {z : V // z ∉ ({z | z ∈ ([u] : List V)} : Set V)} :=
        Equiv.subtypeEquivRight (fun z => by
          simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_singleton])
      have hphi : graphPhi (deleteVertices G ({u} : Set V)) =
          graphPhi (deleteVertices G {z | z ∈ ([u] : List V)}) :=
        graphPhi_equiv (deleteVertices G ({u} : Set V))
          (deleteVertices G {z | z ∈ ([u] : List V)}) e (fun _ _ => Iff.rfl)
      refine ((graph_adjugate_diagonal G u).trans hphi).trans ?_
      exact graphPhi_instances_eq _ _ _ _ _
    | @cons u x v hx q =>
      obtain ⟨hq, hu⟩ := (Walk.cons_isPath_iff hx q).mp hp
      let q' : (G.induce {z | z ≠ u}).Walk
          ⟨x, fun he => hu (he ▸ q.start_mem_support)⟩
          ⟨v, fun he => hu (he ▸ q.end_mem_support)⟩ := punctureWalk u q hu
      have hlen : q'.length < n := by
        have he : q'.length = q.length := punctureWalk_length u q hu
        simp only [Walk.length_cons] at hn
        omega
      have hq' : q'.IsPath := punctureWalk_isPath u q hu hq
      have hH : (G.induce {z | z ≠ u}).IsAcyclic := hG.induce {z | z ≠ u}
      let fW : Fintype {z : V // z ≠ u} := inferInstance
      let dW : DecidableEq {z : V // z ≠ u} := inferInstance
      let aH : DecidableRel (G.induce {z | z ≠ u}).Adj := inferInstance
      have hIH := @ih q'.length hlen {z : V // z ≠ u} fW dW
        (G.induce {z | z ≠ u}) aH hH
        ⟨x, fun he => hu (he ▸ q.start_mem_support)⟩
        ⟨v, fun he => hu (he ▸ q.end_mem_support)⟩ q' hq' rfl
      refine (acyclic_adjugate_step G hG hx q hq hu).trans ?_
      refine (graphCofactor_instances_eq _ fW _ dW (G.induce {z | z ≠ u}) _ aH
        ⟨v, fun he => hu (he ▸ q.end_mem_support)⟩
        ⟨x, fun he => hu (he ▸ q.start_mem_support)⟩).trans ?_
      refine hIH.trans ?_
      exact (graphPhi_instances_eq _ _ _ _ _).trans
        (puncture_path_complement_phi G hx q hu)
#print axioms Paper7UnicyclicSchwenk.acyclic_path_cofactor_aux

/-- Arbitrary finite acyclic graphs, not just connected trees or path graphs. -/
theorem acyclic_path_cofactor {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (u v : V) (p : G.Walk u v) (hp : p.IsPath) :
    (Matrix.charmatrix (G.adjMatrix ℤ)).adjugate v u =
      graphPhi (deleteVertices G {z | z ∈ p.support}) :=
  acyclic_path_cofactor_aux p.length V G hG u v p hp rfl
#print axioms Paper7UnicyclicSchwenk.acyclic_path_cofactor

/-- The original tree/path orientation required by the Schwenk cycle-edge
bridge. Zero-length paths and empty remaining graphs are included. -/
theorem tree_path_cofactor {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (u v : V) (p : T.Walk v u) (hp : p.IsPath) :
    (Matrix.charmatrix (T.adjMatrix ℤ)).adjugate v u =
      graphPhi (deleteVertices T {z | z ∈ p.support}) := by
  calc
    (Matrix.charmatrix (T.adjMatrix ℤ)).adjugate v u =
        (Matrix.charmatrix (T.adjMatrix ℤ)).adjugate u v :=
      (graph_charmatrix_isSymm T).adjugate.apply u v
    _ = graphPhi (deleteVertices T {z | z ∈ p.support}) :=
      acyclic_path_cofactor T hT.isAcyclic v u p hp
#print axioms Paper7UnicyclicSchwenk.tree_path_cofactor

end Paper7UnicyclicSchwenk
