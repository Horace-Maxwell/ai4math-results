import Research.TaskH.Seven.SevenBPShortestLongCycle

/-! True two-edge ears through a point outside the actual cycle support. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem path_two_ear_cycle {a b z : V} (p : G.Walk a b) (hp : p.IsPath)
    (hz : z ∉ p.support) (ha : G.Adj a z) (hb : G.Adj b z)
    (hlen : 1 ≤ p.length) :
    (Walk.cons hb (Walk.cons ha.symm p)).IsCycle := by
  have hpath : (Walk.cons ha.symm p).IsPath := hp.cons hz
  exact path_closing_cycle (Walk.cons ha.symm p) hpath hb.symm
    (by simpa only [Walk.length_cons] using Nat.add_le_add_right hlen 1)

theorem shortest_cycle_external_ear_distances (hb : G.IsBipartite) {a z : V}
    (p : G.Walk a a) (hshort : ShortestLongCycle p)
    (hz : z ∉ p.support) (n : ℕ) (hn : 4 ≤ n) (hfar : n + 4 ≤ p.length)
    (ha : G.Adj a z) (hzend : G.Adj (p.getVert n) z) :
    n ≤ 10 ∧ p.length - n ≤ 10 := by
  have htake : (p.take n).length = n := by
    simp only [Walk.take_length, inf_eq_left.mpr (by omega : n ≤ p.length)]
  have hdrop : (p.drop n).length = p.length - n := by
    simp only [Walk.drop_length]
  have hztake : z ∉ (p.take n).support :=
    fun h => hz ((p.isSubwalk_take n).support_subset h)
  have hzdrop : z ∉ (p.drop n).support :=
    fun h => hz ((p.isSubwalk_drop n).support_subset h)
  have hfirst : (Walk.cons hzend (Walk.cons ha.symm (p.take n))).IsCycle :=
    path_two_ear_cycle (p.take n) (hshort.1.isPath_take (by omega)) hztake ha hzend
      (by omega)
  have hsecond : (Walk.cons ha (Walk.cons hzend.symm (p.drop n))).IsCycle :=
    path_two_ear_cycle (p.drop n) (hshort.1.isPath_drop (by omega)) hzdrop hzend ha
      (by omega)
  have hlen1 : (Walk.cons hzend (Walk.cons ha.symm (p.take n))).length = n + 2 := by
    simp only [Walk.length_cons, htake]
  have hlen2 : (Walk.cons ha (Walk.cons hzend.symm (p.drop n))).length =
      p.length - n + 2 := by
    simp only [Walk.length_cons, hdrop]
  have h1 := shorter_cycle_le_twelve hb p hshort _ hfirst (by omega)
  have h2 := shorter_cycle_le_twelve hb p hshort _ hsecond (by omega)
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.path_two_ear_cycle
#print axioms TaskH.Seven.BP.shortest_cycle_external_ear_distances
