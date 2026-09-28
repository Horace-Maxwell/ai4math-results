import Research.AxialMSZ.Proof.ExSSimple
set_option autoImplicit false
namespace CodexAxial.SimpleExample
open AxialMSZ.Challenge

abbrev graph := nonAnnGraph ExS.μ ExS.X
def va : ExS.X := ⟨a,by simp [ExS.X,a]⟩
def vb : ExS.X := ⟨b,by simp [ExS.X,b]⟩
def vc : ExS.X := ⟨c,by simp [ExS.X,c]⟩

theorem vc_ne_va : vc ≠ va := by
  intro h
  have hh := congrArg (fun z : ExS.X => (z : A) 3) h
  norm_num [vc,va,a,c,e] at hh

theorem adjacent_ab : graph.Adj va vb := by
  rw [graph,nonAnnGraph,SimpleGraph.fromRel_adj]
  refine ⟨?_,Or.inl ?_⟩
  · intro h
    have hh := congrArg (fun z : ExS.X => (z : A) 0) h
    norm_num [va,vb,a,b,e] at hh
  · change ExS.μ a b ≠ 0
    intro h
    have hh := congrFun h 2
    rw [a_mul] at hh
    norm_num [b,e] at hh

theorem c_isolated (q : ExS.X) : ¬ graph.Adj vc q := by
  intro h
  rw [graph,nonAnnGraph,SimpleGraph.fromRel_adj] at h
  rcases q with ⟨q,hq⟩
  rcases hq with rfl | rfl | rfl
  · rcases h.2 with hh | hh
    · apply hh
      change ExS.μ c a = 0
      rw [c_mul]
      funext k
      fin_cases k <;> norm_num [a,e]
    · apply hh
      change ExS.μ a c = 0
      rw [a_mul]
      funext k
      fin_cases k <;> norm_num [c,e]
  · rcases h.2 with hh | hh
    · apply hh
      change ExS.μ c b = 0
      rw [c_mul]
      funext k
      fin_cases k <;> norm_num [b,e]
    · apply hh
      change ExS.μ b c = 0
      rw [b_mul]
      funext k
      fin_cases k <;> norm_num [c,e]
  · exact h.1 (Subtype.ext rfl)

theorem c_walk_endpoint {q : ExS.X} (p : graph.Walk vc q) : vc = q := by
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

theorem cx_nonzero : ExS.μ x c ≠ 0 := by
  intro h
  have hh := congrFun h 3
  rw [x_mul] at hh
  norm_num [c,e] at hh

theorem components_do_not_annihilate : ¬ ComponentsAnnihilate ExS.μ ExS.X := by
  intro h
  let C := graph.connectedComponentMk va
  let D := graph.connectedComponentMk vc
  have hca : va ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hcb : vb ∈ C.supp := C.mem_supp_of_adj_mem_supp hca adjacent_ab
  have hdc : vc ∈ D.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have ma : a ∈ gen ExS.μ (Subtype.val '' C.supp) :=
    mem_gen_of_mem ⟨va,hca,rfl⟩
  have mb : b ∈ gen ExS.μ (Subtype.val '' C.supp) :=
    mem_gen_of_mem ⟨vb,hcb,rfl⟩
  have mc : c ∈ gen ExS.μ (Subtype.val '' D.supp) :=
    mem_gen_of_mem ⟨vc,hdc,rfl⟩
  have mx : x ∈ gen ExS.μ (Subtype.val '' C.supp) := by
    rw [x_from_ab]
    exact Submodule.sub_mem _ (Submodule.add_mem _ ma mb)
      (Submodule.smul_mem _ _ (gen_isSubalgebra _ _ _ ma _ mb))
  exact cx_nonzero (h C D components_distinct x mx c mc)

#print axioms disconnected
#print axioms components_do_not_annihilate
end CodexAxial.SimpleExample
