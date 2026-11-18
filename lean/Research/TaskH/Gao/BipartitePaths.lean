import Mathlib

/-! Actual alternating simple paths in two disjoint finite parts with every
cross edge present. No clique edge, path-list or path-family oracle is used. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

theorem finset_bipartite_odd_path_exact (j : ℕ) :
    ∀ (A B : Finset V) (x p : V), Disjoint A B →
      (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) → x ∈ B → p ∈ A →
      j + 1 ≤ A.card → j + 1 ≤ B.card →
      ∃ q : G.Walk x p, q.IsPath ∧ q.length = 2 * j + 1 ∧
        ∀ z ∈ q.support, z ∈ A ∨ z ∈ B := by
  classical
  induction j with
  | zero =>
    intro A B x p _hAB hcross hx hp _hA _hB
    have e : G.Adj x p := (hcross p hp x hx).symm
    refine ⟨e.toWalk, e.isPath_toWalk, e.length_toWalk, ?_⟩
    intro z hz
    rw [SimpleGraph.Adj.support_toWalk] at hz
    have hz' : z = x ∨ z = p := by simpa using hz
    rcases hz' with rfl | rfl
    · exact Or.inr hx
    · exact Or.inl hp
  | succ j ih =>
    intro A B x p hAB hcross hx hp hA hB
    have hAtwo : 1 < A.card := by omega
    obtain ⟨a, ha, hap⟩ := Finset.exists_mem_ne hAtwo p
    let A' := A.erase a
    let B' := B.erase x
    have hAcard : A'.card = A.card - 1 := Finset.card_erase_of_mem ha
    have hBcard : B'.card = B.card - 1 := Finset.card_erase_of_mem hx
    have hBpos : 0 < B'.card := by omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hBpos
    have hp' : p ∈ A' := Finset.mem_erase.mpr ⟨hap.symm, hp⟩
    have hAB' : Disjoint A' B' := by
      apply Finset.disjoint_left.mpr
      intro z hzA hzB
      exact Finset.disjoint_left.mp hAB
        (Finset.mem_of_mem_erase hzA) (Finset.mem_of_mem_erase hzB)
    have hcross' : ∀ a' ∈ A', ∀ b' ∈ B', G.Adj a' b' := by
      intro a' ha' b' hb'
      exact hcross a' (Finset.mem_of_mem_erase ha') b' (Finset.mem_of_mem_erase hb')
    obtain ⟨q, hq, hlen, hsupp⟩ :=
      ih A' B' b p hAB' hcross' hb hp' (by omega) (by omega)
    have hnotA : a ∉ q.support := by
      intro haQ
      rcases hsupp a haQ with haQ | haQ
      · exact (Finset.notMem_erase a A) haQ
      · exact Finset.disjoint_left.mp hAB ha (Finset.mem_of_mem_erase haQ)
    have hnotX : x ∉ q.support := by
      intro hxQ
      rcases hsupp x hxQ with hxQ | hxQ
      · exact Finset.disjoint_left.mp hAB (Finset.mem_of_mem_erase hxQ) hx
      · exact (Finset.notMem_erase x B) hxQ
    have hxa : x ≠ a := by
      intro he
      exact Finset.disjoint_left.mp hAB ha (he ▸ hx)
    have exa : G.Adj x a := (hcross a ha x hx).symm
    have eab : G.Adj a b := hcross a ha b (Finset.mem_of_mem_erase hb)
    have hxTail : x ∉ (Walk.cons eab q).support := by
      rw [Walk.support_cons]
      intro hz
      rcases List.mem_cons.mp hz with he | hz
      · exact hxa he
      · exact hnotX hz
    refine ⟨Walk.cons exa (Walk.cons eab q), (hq.cons hnotA).cons hxTail, ?_, ?_⟩
    · rw [Walk.length_cons, Walk.length_cons, hlen]
      omega
    · intro z hz
      rw [Walk.support_cons] at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inr hx
      · rw [Walk.support_cons] at hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl ha
        · rcases hsupp z hz with hz | hz
          · exact Or.inl (Finset.mem_of_mem_erase hz)
          · exact Or.inr (Finset.mem_of_mem_erase hz)

theorem finset_bipartite_even_path_exact (j : ℕ) (A B : Finset V)
    (x p : V) (hAB : Disjoint A B)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hp : p ∈ B) (hxp : x ≠ p)
    (hA : j + 1 ≤ A.card) (hB : j + 2 ≤ B.card) :
    ∃ q : G.Walk x p, q.IsPath ∧ q.length = 2 * j + 2 ∧
      ∀ z ∈ q.support, z ∈ A ∨ z ∈ B := by
  classical
  have hApos : 0 < A.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hApos
  let B' := B.erase x
  have hBcard : B'.card = B.card - 1 := Finset.card_erase_of_mem hx
  have hp' : p ∈ B' := Finset.mem_erase.mpr ⟨hxp.symm, hp⟩
  have hBA : Disjoint B' A := by
    apply Finset.disjoint_left.mpr
    intro z hzB hzA
    exact Finset.disjoint_left.mp hAB hzA (Finset.mem_of_mem_erase hzB)
  have hcross' : ∀ b ∈ B', ∀ a' ∈ A, G.Adj b a' := by
    intro b hb a' ha'
    exact (hcross a' ha' b (Finset.mem_of_mem_erase hb)).symm
  obtain ⟨q, hq, hlen, hsupp⟩ :=
    finset_bipartite_odd_path_exact j B' A a p hBA hcross' ha hp' (by omega) hA
  have havoid : x ∉ q.support := by
    intro hxQ
    rcases hsupp x hxQ with hxQ | hxQ
    · exact (Finset.notMem_erase x B) hxQ
    · exact Finset.disjoint_left.mp hAB hxQ hx
  have e : G.Adj x a := (hcross a ha x hx).symm
  refine ⟨Walk.cons e q, hq.cons havoid, ?_, ?_⟩
  · rw [Walk.length_cons, hlen]
  · intro z hz
    rw [Walk.support_cons] at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact Or.inr hx
    · rcases hsupp z hz with hz | hz
      · exact Or.inr (Finset.mem_of_mem_erase hz)
      · exact Or.inl hz

#print axioms finset_bipartite_odd_path_exact
#print axioms finset_bipartite_even_path_exact
end TaskH.Gao
