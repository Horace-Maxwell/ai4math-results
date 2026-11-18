import Research.TaskH.Fan.RootedConnectivity

/-! The actual original degree condition excludes every order below four. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem rooted_degree_order_four [Fintype V] (G : SimpleGraph V) (x y : V)
    (hroot : RootedTwoConnected G x y) (hdeg : NonrootDegreeAtLeast G x y 3) :
    4 ≤ Fintype.card V := by
  classical
  obtain ⟨z, hzx, hzy⟩ := exists_vertex_avoiding_two hroot.2.1 x y
  have hd := hdeg z hzx hzy
  rw [G.ncard_neighborSet z] at hd
  have hlt := G.degree_lt_card_verts z
  omega

#print axioms rooted_degree_order_four
end TaskH.Fan
