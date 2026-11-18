import Research.TaskH.Gao.BipartitePaths

/-! Exact uniform prefix families, with the actual attachment endpoint
externally quantified. The finite paths are constructed before choice. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

theorem bipartite_odd_prefix_family (A B : Finset V) (r : ℕ) (x p : V)
    (hAB : Disjoint A B) (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hp : p ∈ A) (hA : r ≤ A.card) (hB : r ≤ B.card) :
    ∃ q : Fin r → G.Walk x p, ∀ i,
      (q i).IsPath ∧ (q i).length = 2 * i.val + 1 ∧
        ∀ z ∈ (q i).support, z ∈ A ∨ z ∈ B := by
  classical
  have hex : ∀ i : Fin r, ∃ q : G.Walk x p,
      q.IsPath ∧ q.length = 2 * i.val + 1 ∧ ∀ z ∈ q.support, z ∈ A ∨ z ∈ B := by
    intro i
    have hi := i.isLt
    exact finset_bipartite_odd_path_exact i.val A B x p hAB hcross hx hp (by omega) (by omega)
  choose q hq using hex
  exact ⟨q, hq⟩

theorem bipartite_even_prefix_family (A B : Finset V) (r : ℕ) (x p : V)
    (hAB : Disjoint A B) (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hp : p ∈ B) (hxp : x ≠ p)
    (hA : r ≤ A.card) (hB : r + 1 ≤ B.card) :
    ∃ q : Fin r → G.Walk x p, ∀ i,
      (q i).IsPath ∧ (q i).length = 2 * i.val + 2 ∧
        ∀ z ∈ (q i).support, z ∈ A ∨ z ∈ B := by
  classical
  have hex : ∀ i : Fin r, ∃ q : G.Walk x p,
      q.IsPath ∧ q.length = 2 * i.val + 2 ∧ ∀ z ∈ q.support, z ∈ A ∨ z ∈ B := by
    intro i
    have hi := i.isLt
    exact finset_bipartite_even_path_exact i.val A B x p hAB hcross hx hp hxp
      (by omega) (by omega)
  choose q hq using hex
  exact ⟨q, hq⟩

theorem bipartite_odd_prefix_family_avoid_two (A B : Finset V) (r : ℕ)
    (x p u w : V) (hAB : Disjoint A B)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hp : p ∈ A) (hu : u ∈ A) (hw : w ∈ B)
    (hxw : x ≠ w) (hpu : p ≠ u) (hA : r + 1 ≤ A.card) (hB : r + 1 ≤ B.card) :
    ∃ q : Fin r → G.Walk x p, ∀ i,
      (q i).IsPath ∧ (q i).length = 2 * i.val + 1 ∧
        (∀ z ∈ (q i).support, z ∈ A ∨ z ∈ B) ∧
          u ∉ (q i).support ∧ w ∉ (q i).support := by
  classical
  let A' := A.erase u
  let B' := B.erase w
  have hAc : A'.card = A.card - 1 := Finset.card_erase_of_mem hu
  have hBc : B'.card = B.card - 1 := Finset.card_erase_of_mem hw
  have hx' : x ∈ B' := Finset.mem_erase.mpr ⟨hxw, hx⟩
  have hp' : p ∈ A' := Finset.mem_erase.mpr ⟨hpu, hp⟩
  have hAB' : Disjoint A' B' := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    exact Finset.disjoint_left.mp hAB
      (Finset.mem_of_mem_erase hzA) (Finset.mem_of_mem_erase hzB)
  have hc' : ∀ a ∈ A', ∀ b ∈ B', G.Adj a b := by
    intro a ha b hb
    exact hcross a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  obtain ⟨q, hq⟩ := bipartite_odd_prefix_family A' B' r x p hAB' hc' hx' hp'
    (by omega) (by omega)
  refine ⟨q, ?_⟩
  intro i
  obtain ⟨hpath, hlen, hsupp⟩ := hq i
  refine ⟨hpath, hlen, ?_, ?_, ?_⟩
  · intro z hz
    rcases hsupp z hz with hz | hz
    · exact Or.inl (Finset.mem_of_mem_erase hz)
    · exact Or.inr (Finset.mem_of_mem_erase hz)
  · intro hz
    rcases hsupp u hz with hz | hz
    · exact (Finset.notMem_erase u A) hz
    · exact Finset.disjoint_left.mp hAB hu (Finset.mem_of_mem_erase hz)
  · intro hz
    rcases hsupp w hz with hz | hz
    · exact Finset.disjoint_left.mp hAB (Finset.mem_of_mem_erase hz) hw
    · exact (Finset.notMem_erase w B) hz

#print axioms bipartite_odd_prefix_family
#print axioms bipartite_even_prefix_family
#print axioms bipartite_odd_prefix_family_avoid_two
end TaskH.Gao
