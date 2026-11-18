import Research.TaskH.Gao.TerminalFragmentExistence

/-!
Actual connected-carrier confinement for terminal fragments. The boundary
is derived to lie in the carrier whenever an interior point and an exterior
point of that carrier are known; no end-block inventory is supplied.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem terminal_walk_endpoint_mem_of_closed (G : SimpleGraph V) (S : Set V)
    (hc : ∀ a ∈ S, ∀ d, G.Adj a d → d ∈ S)
    {a d : V} (P : G.Walk a d) (ha : a ∈ S) : d ∈ S := by
  revert ha
  induction P with
  | nil => intro ha; exact ha
  | @cons a c d e P ih => intro ha; exact ih (hc a ha c e)

theorem terminal_boundary_mem_connected_carrier (G : SimpleGraph V)
    (S I : Set V) (b w : V) (hS : (G.induce S).Connected)
    (hI : I ⊆ S) (hw : w ∈ S) (hwI : w ∉ I)
    (hT : TerminalFragment G I b) : b ∈ S := by
  classical
  by_contra hbS
  obtain ⟨a, haI⟩ := hT.1
  let ar : S := ⟨a, hI haI⟩
  let wr : S := ⟨w, hw⟩
  have hc : ∀ v ∈ ({v : S | v.1 ∈ I} : Set S), ∀ d,
      (G.induce S).Adj v d → d ∈ ({v : S | v.1 ∈ I} : Set S) := by
    intro v hv d evd
    have evd' : G.Adj v.1 d.1 := evd
    rcases hT.2.2.1 v.1 hv d.1 evd' with he | he
    · exact False.elim (hbS (Eq.mp (congrArg (fun q : V => q ∈ S) he) d.2))
    · exact he
  obtain ⟨P, _hP⟩ := hS.exists_isPath ar wr
  exact hwI (terminal_walk_endpoint_mem_of_closed (G.induce S)
    {v : S | v.1 ∈ I} hc P haI)

theorem terminal_boundary_route_in_connected_carrier (G : SimpleGraph V)
    (S I : Set V) (b w : V) (hS : (G.induce S).Connected)
    (hI : I ⊆ S) (hw : w ∈ S) (hwI : w ∉ I)
    (hT : TerminalFragment G I b) :
    b ∈ S ∧ ∃ P : G.Walk b w, P.IsPath ∧
      (∀ v ∈ P.support, v ∈ S ∧ v ∉ I) ∧
      ∀ v ∈ P.support, v ∈ fragmentBlock I b → v = b := by
  classical
  have hbS := terminal_boundary_mem_connected_carrier G S I b w hS hI hw hwI hT
  let br : S := ⟨b, hbS⟩
  let wr : S := ⟨w, hw⟩
  let J : Set S := {v | v.1 ∈ I}
  have hbJ : br ∉ J := hT.2.1
  have hclosed : ∀ a ∈ J, ∀ d, (G.induce S).Adj a d → d = br ∨ d ∈ J := by
    intro a ha d ead
    have ead' : G.Adj a.1 d.1 := ead
    rcases hT.2.2.1 a.1 ha d.1 ead' with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr he
  have hconn := fragment_complement_connected (G.induce S) J br hbJ hclosed hS
  let T : Set S := {v | v ∉ J}
  let bb : T := ⟨br, hbJ⟩
  let ww : T := ⟨wr, hwI⟩
  obtain ⟨p, hp⟩ := hconn.exists_isPath bb ww
  let f : (G.induce S).induce T →g G :=
    { toFun := fun v => v.1.1
      map_rel' := fun e => e }
  have hf : Function.Injective f := by
    intro a d he
    exact Subtype.ext (Subtype.ext he)
  let P : G.Walk b w := p.map f
  have hPS : ∀ v ∈ P.support, v ∈ S ∧ v ∉ I := by
    intro v hv
    change v ∈ (p.map f).support at hv
    rw [Walk.support_map] at hv
    obtain ⟨q, _hq, he⟩ := List.mem_map.mp hv
    have he' : q.1.1 = v := he
    constructor
    · exact Eq.mp (congrArg (fun v : V => v ∈ S) he') q.1.2
    · exact Eq.mp (congrArg (fun v : V => v ∉ I) he') q.2
  refine ⟨hbS, P, (Walk.isPath_map_iff_of_injective hf).mpr hp, hPS, ?_⟩
  intro v hv hvB
  rcases hvB with he | he
  · exact he
  · exact False.elim ((hPS v hv).2 he)

#print axioms terminal_walk_endpoint_mem_of_closed
#print axioms terminal_boundary_mem_connected_carrier
#print axioms terminal_boundary_route_in_connected_carrier
end TaskH.Gao
