import Research.TaskH.Fan.PathOperations

/-!
Normalize a rooted problem by deleting only its actual root edge. The added
edge is still solely a connectivity test. Actual output walks are lifted
through the identity-on-vertices graph inclusion, with unchanged support.
-/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

/-- Same actual vertex type, with precisely the root edge removed if it exists. -/
def rootEdgeDeleted (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  G \ SimpleGraph.edge x y

@[simp]
theorem rootEdgeDeleted_adj (G : SimpleGraph V) (x y a b : V) :
    (rootEdgeDeleted G x y).Adj a b ↔ G.Adj a b ∧ ¬(SimpleGraph.edge x y).Adj a b :=
  Iff.rfl

theorem rootEdgeDeleted_le (G : SimpleGraph V) (x y : V) :
    rootEdgeDeleted G x y ≤ G := by
  intro a b hab
  exact hab.1

theorem rootEdgeDeleted_not_adj (G : SimpleGraph V) (x y : V) :
    ¬(rootEdgeDeleted G x y).Adj x y := by
  intro h
  exact h.2 ((SimpleGraph.edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, h.1.ne⟩)

theorem rootEdgeDeleted_augmentation (G : SimpleGraph V) (x y : V) :
    rootEdgeDeleted G x y ⊔ SimpleGraph.edge x y = G ⊔ SimpleGraph.edge x y := by
  ext a b
  simp only [rootEdgeDeleted, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
  tauto

theorem rootEdgeDeleted_eq_self_of_not_adj (G : SimpleGraph V) (x y : V)
    (hxy : ¬G.Adj x y) : rootEdgeDeleted G x y = G := by
  ext a b
  change (G.Adj a b ∧ ¬(SimpleGraph.edge x y).Adj a b) ↔ G.Adj a b
  constructor
  · exact And.left
  · intro hab
    refine ⟨hab, ?_⟩
    intro he
    rcases (SimpleGraph.edge_adj x y a b).mp he with ⟨he, _hne⟩
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy hab
    · exact hxy hab.symm

theorem rootEdgeDeleted_neighborSet (G : SimpleGraph V) (x y v : V)
    (hvx : v ≠ x) (hvy : v ≠ y) :
    (rootEdgeDeleted G x y).neighborSet v = G.neighborSet v := by
  ext w
  change (G.Adj v w ∧ ¬(SimpleGraph.edge x y).Adj v w) ↔ G.Adj v w
  constructor
  · exact And.left
  · intro hvw
    refine ⟨hvw, ?_⟩
    intro he
    rcases (SimpleGraph.edge_adj x y v w).mp he with ⟨he, _hne⟩
    rcases he with he | he
    · exact hvx he.1
    · exact hvy he.1

theorem rootEdgeDeleted_neighbor_ncard (G : SimpleGraph V) (x y v : V)
    (hvx : v ≠ x) (hvy : v ≠ y) :
    ((rootEdgeDeleted G x y).neighborSet v).ncard = (G.neighborSet v).ncard :=
  congrArg Set.ncard (rootEdgeDeleted_neighborSet G x y v hvx hvy)

theorem rootEdgeDeleted_nonroot_degree (G : SimpleGraph V) (x y : V) (d : ℕ)
    (h : NonrootDegreeAtLeast G x y d) :
    NonrootDegreeAtLeast (rootEdgeDeleted G x y) x y d := by
  intro v hvx hvy
  rw [rootEdgeDeleted_neighbor_ncard G x y v hvx hvy]
  exact h v hvx hvy

theorem rootEdgeDeleted_rooted_two_connected [Fintype V] (G : SimpleGraph V)
    (x y : V) (h : RootedTwoConnected G x y) :
    RootedTwoConnected (rootEdgeDeleted G x y) x y := by
  refine ⟨h.1, ?_⟩
  rw [rootEdgeDeleted_augmentation]
  exact h.2

/-- Inclusion uses the actual original edges and is literally identity on vertices. -/
def rootEdgeDeletedInclusion (G : SimpleGraph V) (x y : V) :
    rootEdgeDeleted G x y →g G :=
  SimpleGraph.Hom.ofLE (rootEdgeDeleted_le G x y)

theorem rootEdgeDeleted_witness_lift (G : SimpleGraph V) (x y : V)
    (p q : (rootEdgeDeleted G x y).Walk x y) (hpq : TwoPathWitness p q) :
    TwoPathWitness (p.map (rootEdgeDeletedInclusion G x y))
        (q.map (rootEdgeDeletedInclusion G x y)) ∧
      (p.map (rootEdgeDeletedInclusion G x y)).length = p.length ∧
      (q.map (rootEdgeDeletedInclusion G x y)).length = q.length ∧
      (p.map (rootEdgeDeletedInclusion G x y)).support = p.support ∧
      (q.map (rootEdgeDeletedInclusion G x y)).support = q.support := by
  have hf : Function.Injective (rootEdgeDeletedInclusion G x y) := fun _ _ h => h
  refine ⟨twoPathWitness_map (rootEdgeDeletedInclusion G x y) hf p q hpq,
    Walk.length_map (p := p) (f := rootEdgeDeletedInclusion G x y),
    Walk.length_map (p := q) (f := rootEdgeDeletedInclusion G x y), ?_, ?_⟩
  · exact Walk.support_mapLe_eq_support (rootEdgeDeleted_le G x y) p
  · exact Walk.support_mapLe_eq_support (rootEdgeDeleted_le G x y) q

theorem hasTwoPaths_of_rootEdgeDeleted (G : SimpleGraph V) (x y : V)
    (h : HasTwoPaths (rootEdgeDeleted G x y) x y) : HasTwoPaths G x y := by
  obtain ⟨p, q, hpq⟩ := h
  exact ⟨p.map (rootEdgeDeletedInclusion G x y),
    q.map (rootEdgeDeletedInclusion G x y),
    (rootEdgeDeleted_witness_lift G x y p q hpq).1⟩

/-- A conditional reduction, not an asserted proof of the nonadjacent-root case. -/
theorem twoPathClaim_of_nonadjacent
    (hcore : ∀ (W : Type u) [Fintype W] (G : SimpleGraph W) (x y : W),
      ¬G.Adj x y → RootedTwoConnected G x y → NonrootDegreeAtLeast G x y 3 →
        HasTwoPaths G x y) : TwoPathClaim.{u} := by
  intro W inst G x y hroot hdeg
  apply hasTwoPaths_of_rootEdgeDeleted G x y
  exact hcore W (rootEdgeDeleted G x y) x y (rootEdgeDeleted_not_adj G x y)
    (rootEdgeDeleted_rooted_two_connected G x y hroot)
    (rootEdgeDeleted_nonroot_degree G x y 3 hdeg)

#print axioms rootEdgeDeleted
#print axioms rootEdgeDeleted_adj
#print axioms rootEdgeDeleted_le
#print axioms rootEdgeDeleted_not_adj
#print axioms rootEdgeDeleted_augmentation
#print axioms rootEdgeDeleted_eq_self_of_not_adj
#print axioms rootEdgeDeleted_neighborSet
#print axioms rootEdgeDeleted_neighbor_ncard
#print axioms rootEdgeDeleted_nonroot_degree
#print axioms rootEdgeDeleted_rooted_two_connected
#print axioms rootEdgeDeletedInclusion
#print axioms rootEdgeDeleted_witness_lift
#print axioms hasTwoPaths_of_rootEdgeDeleted
#print axioms twoPathClaim_of_nonadjacent
end TaskH.Fan
