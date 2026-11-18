import Research.TaskH.Fan.PathOperations

/-! Actual complete-subgraph paths by length induction. Erasing the starting
vertex before recursion proves freshness, rather than assuming a path list. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

/-- Every allowed positive length is realized inside the actual finite clique,
with both endpoints fixed. The recursive path lies in K.erase x, so prepending
x preserves simplicity and increases its exact length by one. -/
theorem finset_clique_path_exact (n : ℕ) :
    ∀ (K : Finset V) (x u : V), G.IsClique (K : Set V) → x ∈ K → u ∈ K → x ≠ u →
      1 ≤ n → n < K.card →
      ∃ p : G.Walk x u, p.IsPath ∧ p.length = n ∧ ∀ z ∈ p.support, z ∈ K := by
  classical
  induction n with
  | zero =>
    intro K x u hK hx hu hxu hn hcard
    omega
  | succ n ih =>
    intro K x u hK hx hu hxu hn hcard
    by_cases hn0 : n = 0
    · subst n
      have e : G.Adj x u := hK hx hu hxu
      refine ⟨e.toWalk, e.isPath_toWalk, e.length_toWalk, ?_⟩
      intro z hz
      rw [SimpleGraph.Adj.support_toWalk] at hz
      have hz' : z = x ∨ z = u := by simpa using hz
      rcases hz' with rfl | rfl
      · exact hx
      · exact hu
    · let L : Finset V := K.erase x
      have hLcard : L.card = K.card - 1 := Finset.card_erase_of_mem hx
      have huL : u ∈ L := Finset.mem_erase.mpr ⟨hxu.symm, hu⟩
      have hLtwo : 1 < L.card := by omega
      obtain ⟨v, hvL, hvu⟩ := Finset.exists_mem_ne hLtwo u
      have hKL : G.IsClique (L : Set V) := by
        intro a ha b hb hab
        exact hK (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab
      obtain ⟨p, hp, hlen, hsupp⟩ :=
        ih L v u hKL hvL huL hvu (by omega) (by omega)
      have hxL : x ∉ L := Finset.notMem_erase x K
      have havoid : x ∉ p.support := fun hz => hxL (hsupp x hz)
      have hxv : x ≠ v := by
        intro he
        subst v
        exact hxL hvL
      have ev : G.Adj x v := hK hx (Finset.mem_of_mem_erase hvL) hxv
      refine ⟨Walk.cons ev p, hp.cons havoid, ?_, ?_⟩
      · rw [Walk.length_cons, hlen]
      · intro z hz
        rw [Walk.support_cons] at hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact Finset.mem_of_mem_erase (hsupp z hz)

#print axioms finset_clique_path_exact
end TaskH.Gao
