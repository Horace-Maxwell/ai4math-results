import Research.TaskH.Gao.TerminalFragmentDescent

/-!
A terminal fragment is extracted from actual finite connected-graph data.
The output asserts no maximal-block decomposition or linkage theorem.
All deletion connectedness is derived by the strict component descent.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

def TerminalFragment (G : SimpleGraph V) (I : Set V) (b : V) : Prop :=
  I.Nonempty ∧ b ∉ I ∧
    (∀ a ∈ I, ∀ d, G.Adj a d → d = b ∨ d ∈ I) ∧
    (G.induce I).Connected ∧ (G.induce {v | v ∉ I}).Connected ∧
    (G.induce (fragmentBlock I b)).Connected ∧
    (∀ c ∈ I, (G.induce {v | v ≠ c}).Connected) ∧
    ∀ w : fragmentBlock I b,
      ((G.induce (fragmentBlock I b)).induce {v | v ≠ w}).Connected

theorem terminal_fragment_in_deleted_component [Fintype V] (G : SimpleGraph V)
    (z : V) (C : (G.induce {v | v ≠ z}).ConnectedComponent) (hG : G.Connected) :
    ∃ (b : V) (D : (G.induce {v | v ≠ b}).ConnectedComponent),
      deletedInterior G b D ⊆ deletedInterior G z C ∧
        TerminalFragment G (deletedInterior G b D) b := by
  obtain ⟨b, D, hsub, hmin⟩ := minimal_deletedInterior_exists G z C
  have hn := minimal_deletedInterior_noncut G (deletedInterior G z C) b D hsub hmin hG
  refine ⟨b, D, hsub, deletedInterior_nonempty G b D,
    deletedInterior_root_not_mem G b D, deletedInterior_closed G b D,
    deletedInterior_connected G b D, deletedInterior_complement_connected G b D hG,
    deletedBlock_connected G b D hG, hn, ?_⟩
  intro w
  by_cases hw : w.1 = b
  · have he : w = (⟨b, Or.inl rfl⟩ : fragmentBlock (deletedInterior G b D) b) :=
      Subtype.ext hw
    subst w
    exact deletedBlock_delete_boundary_connected G b D
  · have hwI : w.1 ∈ deletedInterior G b D := by
      rcases w.2 with he | he
      · exact False.elim (hw he)
      · exact he
    exact TaskH.Fan.rootedSet_delete_connected G (fragmentBlock (deletedInterior G b D) b)
      b (Or.inl rfl) (fragmentBlock_closed G _ b (deletedInterior_closed G b D))
      w hw (hn w.1 hwI)

theorem terminal_fragment_exists [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) (hG : G.Connected) :
    ∃ (I : Set V) (b : V), TerminalFragment G I b := by
  obtain ⟨z⟩ := hG.nonempty
  obtain ⟨a, haz⟩ := exists_ne z
  let C := (G.induce {v | v ≠ z}).connectedComponentMk ⟨a, haz⟩
  obtain ⟨b, D, _hsub, hD⟩ := terminal_fragment_in_deleted_component G z C hG
  exact ⟨deletedInterior G b D, b, hD⟩

theorem terminalFragment_block_ncard [Fintype V] (G : SimpleGraph V)
    (I : Set V) (b : V) (h : TerminalFragment G I b) :
    2 ≤ (fragmentBlock I b).ncard := by
  have hi : 0 < I.ncard := (Set.ncard_pos (Set.toFinite _)).mpr h.1
  rw [fragmentBlock_ncard I b h.2.1]
  omega

theorem terminalFragment_twoConnected [Fintype V] (G : SimpleGraph V)
    (I : Set V) (b : V) [Fintype (fragmentBlock I b)]
    (h : TerminalFragment G I b) (hI : 2 ≤ I.ncard) :
    TaskH.Fan.TwoConnected (G.induce (fragmentBlock I b)) := by
  obtain ⟨a, d, ha, hd, had⟩ :=
    (Set.one_lt_ncard_iff (s := I)).mp (show 1 < I.ncard by omega)
  let br : fragmentBlock I b := ⟨b, Or.inl rfl⟩
  let ar : fragmentBlock I b := ⟨a, Or.inr ha⟩
  let dr : fragmentBlock I b := ⟨d, Or.inr hd⟩
  have hba : br ≠ ar := by
    intro he
    have he' : b = a := congrArg Subtype.val he
    apply h.2.1
    rw [he']
    exact ha
  have hbd : br ≠ dr := by
    intro he
    have he' : b = d := congrArg Subtype.val he
    apply h.2.1
    rw [he']
    exact hd
  have had' : ar ≠ dr := fun he => had (congrArg Subtype.val he)
  have hcard : 2 < Fintype.card (fragmentBlock I b) :=
    Fintype.two_lt_card_iff.mpr ⟨br, ar, dr, hba, hbd, had'⟩
  rcases h with ⟨_hne, _hb, _hc, _hi, _hcomp, hB, _hn, hdel⟩
  exact ⟨by omega, hB, hdel⟩

theorem terminalFragment_singleton_bridge (G : SimpleGraph V) (a b : V)
    (hG : G.Connected) (h : TerminalFragment G {a} b) :
    G.Adj a b ∧ G.IsBridge s(a, b) ∧ G.neighborSet a = {b} ∧
      fragmentBlock ({a} : Set V) b = {a, b} := by
  have hab : a ≠ b := by
    intro he
    exact h.2.1 (by simp only [Set.mem_singleton_iff, he])
  have hall : ∀ d, G.Adj a d → d = b := by
    intro d hadj
    rcases h.2.2.1 a (by simp only [Set.mem_singleton_iff]) d hadj with hd | hd
    · exact hd
    · change d = a at hd
      subst d
      exact False.elim (G.irrefl hadj)
  obtain ⟨d, hadj⟩ := (hG a b).nonempty_neighborSet_left hab
  have habadj : G.Adj a b := (hall d hadj) ▸ hadj
  refine ⟨habadj, ?_, ?_, ?_⟩
  · apply SimpleGraph.isBridge_iff.mpr
    intro hr
    obtain ⟨d, hadj⟩ := hr.nonempty_neighborSet_left hab
    have hd := SimpleGraph.deleteEdges_adj.mp hadj
    have he := hall d hd.1
    subst d
    exact hd.2 (by simp only [Set.mem_singleton_iff])
  · ext d
    constructor
    · exact hall d
    · intro hd
      change d = b at hd
      exact hd.symm ▸ habadj
  · ext d
    change (d = b ∨ d = a) ↔ (d = a ∨ d = b)
    exact or_comm

theorem terminalFragment_dichotomy [Fintype V] (G : SimpleGraph V)
    (I : Set V) (b : V) [Fintype (fragmentBlock I b)]
    (hG : G.Connected) (h : TerminalFragment G I b) :
    (∃ a : V, I = {a} ∧ G.Adj a b ∧ G.IsBridge s(a, b) ∧
      fragmentBlock I b = {a, b}) ∨
      TaskH.Fan.TwoConnected (G.induce (fragmentBlock I b)) := by
  by_cases hI : 2 ≤ I.ncard
  · exact Or.inr (terminalFragment_twoConnected G I b h hI)
  · have hp : 0 < I.ncard := (Set.ncard_pos (Set.toFinite _)).mpr h.1
    have hone : I.ncard = 1 := by omega
    obtain ⟨a, he⟩ := Set.ncard_eq_one.mp hone
    have h' : TerminalFragment G {a} b := he ▸ h
    obtain ⟨hadj, hbridge, _hn, hblock⟩ := terminalFragment_singleton_bridge G a b hG h'
    left
    refine ⟨a, he, hadj, hbridge, ?_⟩
    rw [he]
    exact hblock

#print axioms TerminalFragment
#print axioms terminal_fragment_in_deleted_component
#print axioms terminal_fragment_exists
#print axioms terminalFragment_block_ncard
#print axioms terminalFragment_twoConnected
#print axioms terminalFragment_singleton_bridge
#print axioms terminalFragment_dichotomy
end TaskH.Gao
