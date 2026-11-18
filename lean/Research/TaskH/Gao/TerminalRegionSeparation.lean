import Research.TaskH.Gao.TerminalFragmentExistence
import Research.TaskH.Gao.CarrierGreatestRegion

/-! Genuine terminal interiors cannot be crossed by an ordinary two-connected region.
These are local topology lemmas, not a new premise for the original Gao theorem. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem terminal_walk_stays_without_boundary (G : SimpleGraph V)
    (I : Set V) (b : V) (h : TerminalFragment G I b)
    {a d : {v : V // v ≠ b}} (p : (G.induce {v | v ≠ b}).Walk a d)
    (ha : a.1 ∈ I) : d.1 ∈ I := by
  revert ha
  induction p with
  | nil => intro ha; exact ha
  | @cons a c d e p ih =>
    intro ha
    have e' : G.Adj a.1 c.1 := e
    rcases h.2.2.1 a.1 ha c.1 e' with hc | hc
    · exact False.elim (c.2 hc)
    · exact ih hc

theorem terminal_twoConnected_region_subset [Fintype V]
    (G : SimpleGraph V) (I : Set V) (b : V) (h : TerminalFragment G I b)
    (T : Set V) [Fintype T] (hT : TwoConnected (G.induce T))
    (p : V) (hp : p ∈ I) (hpT : p ∈ T) : T ⊆ fragmentBlock I b := by
  classical
  intro q hqT
  by_cases hqb : q = b
  · exact Or.inl hqb
  · have hpb : p ≠ b := by
      intro he
      exact h.2.1 (Eq.mp (congrArg (fun v : V => v ∈ I) he) hp)
    have hr := twoConnected_region_reachable_avoiding G T hT b
      ⟨p, hpT⟩ ⟨q, hqT⟩ hpb hqb
    obtain ⟨r⟩ := hr
    exact Or.inr (terminal_walk_stays_without_boundary G I b h r hp)

theorem terminal_block_inclusion_maximal [Fintype V]
    (G : SimpleGraph V) (I : Set V) (b : V) (h : TerminalFragment G I b)
    (T : Set V) [Fintype T] (hT : TwoConnected (G.induce T))
    (hBT : fragmentBlock I b ⊆ T) : T ⊆ fragmentBlock I b := by
  obtain ⟨p, hp⟩ := h.1
  exact terminal_twoConnected_region_subset G I b h T hT p hp (hBT (Or.inr hp))

theorem terminal_block_boundary_cut (G : SimpleGraph V)
    (I : Set V) (b : V) (h : TerminalFragment G I b)
    (q : V) (hq : q ∉ fragmentBlock I b) :
    ¬(G.induce {v | v ≠ b}).Connected := by
  intro hc
  obtain ⟨p, hp⟩ := h.1
  have hpb : p ≠ b := by
    intro he
    exact h.2.1 (Eq.mp (congrArg (fun v : V => v ∈ I) he) hp)
  have hqb : q ≠ b := fun he => hq (Or.inl he)
  obtain ⟨r⟩ := hc ⟨p, hpb⟩ ⟨q, hqb⟩
  exact hq (Or.inr (terminal_walk_stays_without_boundary G I b h r hp))

theorem terminal_block_eq_univ_of_twoConnected [Fintype V]
    (G : SimpleGraph V) (I : Set V) (b : V)
    (h : TerminalFragment G I b) (hG : TwoConnected G) :
    fragmentBlock I b = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro q
  by_cases hqb : q = b
  · exact Or.inl hqb
  · obtain ⟨p, hp⟩ := h.1
    have hpb : p ≠ b := by
      intro he
      exact h.2.1 (Eq.mp (congrArg (fun v : V => v ∈ I) he) hp)
    obtain ⟨r⟩ := hG.2.2 b ⟨p, hpb⟩ ⟨q, hqb⟩
    exact Or.inr (terminal_walk_stays_without_boundary G I b h r hp)

theorem terminal_twoConnected_region_avoids_interior [Fintype V]
    (G : SimpleGraph V) (I : Set V) (b : V) (h : TerminalFragment G I b)
    (T : Set V) [Fintype T] (hT : TwoConnected (G.induce T))
    (q : V) (hqT : q ∈ T) (hqB : q ∉ fragmentBlock I b) : Disjoint T I := by
  apply Set.disjoint_left.mpr
  intro p hpT hpI
  exact hqB (terminal_twoConnected_region_subset G I b h T hT p hpI hpT hqT)

#print axioms terminal_walk_stays_without_boundary
#print axioms terminal_twoConnected_region_subset
#print axioms terminal_block_inclusion_maximal
#print axioms terminal_block_boundary_cut
#print axioms terminal_block_eq_univ_of_twoConnected
#print axioms terminal_twoConnected_region_avoids_interior
end TaskH.Gao
