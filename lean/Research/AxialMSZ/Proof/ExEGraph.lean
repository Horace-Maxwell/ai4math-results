import Research.AxialMSZ.Proof.ExEBlocks
set_option autoImplicit false
namespace CodexAxial.DominanceExample
open AxialMSZ.Challenge

abbrev graph := nonAnnGraph ExE.μ ExE.X
def va : ExE.X := ⟨a,by simp [ExE.X,a]⟩
def vb : ExE.X := ⟨b,by simp [ExE.X,b]⟩
def vc : ExE.X := ⟨c,by simp [ExE.X,c]⟩

theorem vc_ne_va : vc ≠ va := by
  intro h
  have hh := congrArg (fun z : ExE.X => (z : A) 3) h
  norm_num [vc,va,a,c,e] at hh

theorem adjacent_ab : graph.Adj va vb := by
  rw [graph,nonAnnGraph,SimpleGraph.fromRel_adj]
  refine ⟨?_,Or.inl ?_⟩
  · intro h
    have hh := congrArg (fun z : ExE.X => (z : A) 0) h
    norm_num [va,vb,a,b,e] at hh
  · change ExE.μ a b ≠ 0
    intro h
    have hh := congrFun h 2
    rw [a_mul] at hh
    norm_num [b,e] at hh

theorem c_isolated (q : ExE.X) : ¬ graph.Adj vc q := by
  intro h
  rw [graph,nonAnnGraph,SimpleGraph.fromRel_adj] at h
  rcases q with ⟨q,hq⟩
  rcases hq with rfl | rfl | rfl
  · rcases h.2 with hh | hh
    · apply hh
      change ExE.μ c a = 0
      rw [c_mul]
      funext k
      fin_cases k <;> norm_num [a,e]
    · apply hh
      change ExE.μ a c = 0
      rw [a_mul]
      funext k
      fin_cases k <;> norm_num [c,e]
  · rcases h.2 with hh | hh
    · apply hh
      change ExE.μ c b = 0
      rw [c_mul]
      funext k
      fin_cases k <;> norm_num [b,e]
    · apply hh
      change ExE.μ b c = 0
      rw [b_mul]
      funext k
      fin_cases k <;> norm_num [c,e]
  · exact h.1 (Subtype.ext rfl)

theorem c_walk_endpoint {q : ExE.X} (p : graph.Walk vc q) : vc = q := by
  cases p with
  | nil => rfl
  | cons h _ => exact (c_isolated _ h).elim

theorem disconnected : ¬ graph.Connected := by
  intro h
  obtain ⟨p⟩ := h.preconnected vc va
  exact vc_ne_va (c_walk_endpoint p)

theorem components_distinct : graph.connectedComponentMk va ≠ graph.connectedComponentMk vc := by
  intro h
  have hr := SimpleGraph.ConnectedComponent.exact h.symm
  obtain ⟨p⟩ := hr
  exact vc_ne_va (c_walk_endpoint p)

theorem cx_nonzero : ExE.μ x c ≠ 0 := by
  intro h
  have hh := congrFun h 2
  rw [x_mul] at hh
  norm_num [c,e] at hh

theorem components_do_not_annihilate : ¬ ComponentsAnnihilate ExE.μ ExE.X := by
  intro h
  let C := graph.connectedComponentMk va
  let D := graph.connectedComponentMk vc
  have hca : va ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hcb : vb ∈ C.supp := C.mem_supp_of_adj_mem_supp hca adjacent_ab
  have hdc : vc ∈ D.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have ma : a ∈ gen ExE.μ (Subtype.val '' C.supp) :=
    mem_gen_of_mem ⟨va,hca,rfl⟩
  have mb : b ∈ gen ExE.μ (Subtype.val '' C.supp) :=
    mem_gen_of_mem ⟨vb,hcb,rfl⟩
  have mc : c ∈ gen ExE.μ (Subtype.val '' D.supp) :=
    mem_gen_of_mem ⟨vc,hdc,rfl⟩
  have mx : x ∈ gen ExE.μ (Subtype.val '' C.supp) := by
    rw [x_from_ab]
    exact Submodule.sub_mem _ (Submodule.add_mem _ ma mb)
      (Submodule.smul_mem _ _ (gen_isSubalgebra _ _ _ ma _ mb))
  exact cx_nonzero (h C D components_distinct x mx c mc)

#print axioms disconnected
#print axioms components_do_not_annihilate
end CodexAxial.DominanceExample
