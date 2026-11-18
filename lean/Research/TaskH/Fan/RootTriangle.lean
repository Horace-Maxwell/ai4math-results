import Research.TaskH.Fan.TriangleFirstHit
import Research.TaskH.Fan.TrianglePrefixes

/-! Root triangles internally produce the exact original two-path witness. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem root_triangle_hasTwoPaths [Fintype V] (G : SimpleGraph V) (x y u v : V)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (exu : G.Adj x u) (euv : G.Adj u v) (evx : G.Adj v x) : HasTwoPaths G x y := by
  have huy : u ≠ y := fun he => hno (he ▸ exu)
  have hvy : v ≠ y := fun he => hno (he ▸ evx.symm)
  obtain ⟨p, hp, r, hr, hrl, hs⟩ := deleted_two_vertex_first_hit G x y u v
    hxy.symm exu.ne.symm evx.ne huy hvy euv.ne (hG.2.2 x)
  rcases hp with hpu | hpv
  · subst p
    exact triangle_positive_tail G x u v y exu.ne evx.ne.symm euv.ne exu euv evx r hr hrl hs
  · subst p
    apply triangle_positive_tail G x v u y evx.ne.symm exu.ne euv.ne.symm
      evx.symm euv.symm exu.symm r hr hrl
    intro w hw hwv
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]
      using hs w hw hwv

theorem counterexample_root_no_triangle [Fintype V] (G : SimpleGraph V) (x y : V)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y) (hbad : ¬HasTwoPaths G x y) :
    ∀ u v, G.Adj x u → G.Adj u v → G.Adj v x → False := by
  intro u v exu euv evx
  exact hbad (root_triangle_hasTwoPaths G x y u v hG hxy hno exu euv evx)

theorem counterexample_neighbor_independent [Fintype V] (G : SimpleGraph V) (x y : V)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y) (hbad : ¬HasTwoPaths G x y) :
    G.IsIndepSet (G.neighborSet x) := by
  intro u hu v hv _huv euv
  exact counterexample_root_no_triangle G x y hG hxy hno hbad u v hu euv hv.symm

theorem counterexample_both_neighbors_independent [Fintype V] (G : SimpleGraph V) (x y : V)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y) (hbad : ¬HasTwoPaths G x y) :
    G.IsIndepSet (G.neighborSet x) ∧ G.IsIndepSet (G.neighborSet y) := by
  refine ⟨counterexample_neighbor_independent G x y hG hxy hno hbad, ?_⟩
  exact counterexample_neighbor_independent G y x hG hxy.symm
    (fun e => hno e.symm) (fun h => hbad (hasTwoPaths_reverse h))

#print axioms root_triangle_hasTwoPaths
#print axioms counterexample_root_no_triangle
#print axioms counterexample_neighbor_independent
#print axioms counterexample_both_neighbors_independent
end TaskH.Fan
