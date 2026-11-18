import Research.TaskH.Fan.BoundaryQuotientConnectivity
import Research.TaskH.Fan.IdentificationPathLift

/-! Each quotient path lifts to a full original path with exactly two real added edges. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem equalBranch_path_lift (G : SimpleGraph V) (x y w u : V)
    (hxy : x ≠ y) (hno : ¬G.Adj x y) (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y)
    (hu : u ∈ equalBranchBoundary G (equalNeighborhoodRegion G x w hw))
    (p : (equalBranchGraph G x w hw u).Walk none
      (some (boundaryRetainedRoot G (equalNeighborhoodRegion G x w hw) u hu)))
    (hp : p.IsPath) :
    ∃ P : G.Walk x y, P.IsPath ∧ P.length = p.length + 2 := by
  let D := equalNeighborhoodRegion G x w hw
  let A := equalBranchDomain G x w hw
  let C := equalBranchCollapsed G x w hw u
  let ur := boundaryRetainedRoot G D u hu
  obtain ⟨s, hs, q, hq, hqlen, _hqs⟩ :=
    identification_path_lift (G.induce A) C ur p hp
  let f : G.induce A →g G := (SimpleGraph.Embedding.induce A).toHom
  let q' : G.Walk s.1 u := q.map f
  have hq' : q'.IsPath := by
    change (q.map f).IsPath
    exact (Walk.isPath_map_iff_of_injective (f := f) Subtype.val_injective).mpr hq
  have hq'len : q'.length = p.length := by
    change (q.map f).length = p.length
    exact (Walk.length_map (p := q) (f := f)).trans hqlen
  let r : G.Walk u s.1 := q'.reverse
  have hr : r.IsPath := hq'.reverse
  have hsub : ∀ v ∈ r.support, v ∈ A := by
    intro v hv
    have hvr : v ∈ q'.reverse.support := hv
    rw [Walk.support_reverse q'] at hvr
    have hvq : v ∈ q'.support := List.mem_reverse.mp hvr
    have hv' : v ∈ (q.map f).support := hvq
    rw [Walk.support_map] at hv'
    obtain ⟨a, _ha, hav⟩ := List.mem_map.mp hv'
    have haA : f a ∈ A := a.2
    exact hav ▸ haA
  have havoid := equalBranchDomain_avoids_roots G x y w hno heq hw hwx hwy
  have hx : x ∉ r.support := fun h => havoid.1 (hsub x h)
  have exu : G.Adj x u := equalBranchBoundary_subset G x w hw hu
  have esN : s.1 ∈ G.neighborSet x := equalBranchBoundary_subset G x w hw hs.1
  have esNy : s.1 ∈ G.neighborSet y :=
    Eq.mpr (congrArg (fun T : Set V => s.1 ∈ T) heq) esN
  have eys : G.Adj y s.1 := esNy
  let a : G.Walk x s.1 := Walk.cons exu r
  have ha : a.IsPath := by
    change (Walk.cons exu r).IsPath
    exact (Walk.cons_isPath_iff exu r).mpr ⟨hr, hx⟩
  have hy : y ∉ a.support := by
    intro hy
    have hy' : y = x ∨ y ∈ r.support := by
      simpa only [a, Walk.support_cons, List.mem_cons] using hy
    rcases hy' with hyx | hyr
    · exact hxy hyx.symm
    · exact havoid.2 (hsub y hyr)
  let P : G.Walk x y := a.concat eys.symm
  refine ⟨P, ha.concat hy eys.symm, ?_⟩
  have hlen : r.length = p.length := (Walk.length_reverse q').trans hq'len
  simp only [P, Walk.length_concat, a, Walk.length_cons]
  omega

theorem equalBranch_two_path_lift (G : SimpleGraph V) (x y w u : V)
    (hxy : x ≠ y) (hno : ¬G.Adj x y) (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y)
    (hu : u ∈ equalBranchBoundary G (equalNeighborhoodRegion G x w hw))
    (h : HasTwoPaths (equalBranchGraph G x w hw u) none
      (some (boundaryRetainedRoot G (equalNeighborhoodRegion G x w hw) u hu))) :
    HasTwoPaths G x y := by
  obtain ⟨p, q, hp, hq, hp2, hq2, hgap⟩ := h
  obtain ⟨P, hP, hPlen⟩ := equalBranch_path_lift G x y w u hxy hno heq hw hwx hwy hu p hp
  obtain ⟨Q, hQ, hQlen⟩ := equalBranch_path_lift G x y w u hxy hno heq hw hwx hwy hu q hq
  refine ⟨P, Q, hP, hQ, ?_, ?_, ?_⟩
  · omega
  · omega
  · rcases hgap with hgap | hgap
    · left
      omega
    · right
      omega

#print axioms equalBranch_path_lift
#print axioms equalBranch_two_path_lift
end TaskH.Fan
