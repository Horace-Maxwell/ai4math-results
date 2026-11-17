import Mathlib

/-! The longest-path step of BP45, proved on the actual graph.
It uses only finiteness, bipartiteness, and degree at least seven.
No small-order, criticality, or supplied cycle premise is needed here. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

theorem maximal_path_neighbor_mem {a b z : V} (p : G.Walk a b) (hp : p.IsPath)
    (hmax : ∀ (s t : V) (q : G.Walk s t), q.IsPath → q.length ≤ p.length)
    (haz : G.Adj a z) : z ∈ p.support := by
  by_contra hz
  have hq : (Walk.cons haz.symm p).IsPath := hp.cons hz
  have hlen := hmax z b (Walk.cons haz.symm p) hq
  simp only [Walk.length_cons] at hlen
  omega

theorem adjacent_path_index_odd (c : G.Coloring Bool) {a b : V} (p : G.Walk a b)
    (n : ℕ) (hn : n ≤ p.length) (ha : G.Adj a (p.getVert n)) : n % 2 = 1 := by
  have hnot : ¬Even n := by
    intro heven
    have hc : c a ↔ c (p.getVert n) := by
      apply (c.even_length_iff_congr (p.take n)).mp
      simpa only [Walk.take_length, inf_eq_left.mpr hn] using heven
    have hne := c.valid ha
    cases h1 : c a <;> cases h2 : c (p.getVert n) <;> simp_all
  exact Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hnot)

theorem maximal_path_far_neighbor [Fintype V] (c : G.Coloring Bool)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hmax : ∀ (s t : V) (q : G.Walk s t), q.IsPath → q.length ≤ p.length)
    (hd : 7 ≤ G.degree a) :
    ∃ n : ℕ, 13 ≤ n ∧ n ≤ p.length ∧ G.Adj a (p.getVert n) := by
  classical
  by_contra hnone
  have hsmall (n : ℕ) (hn : n ≤ p.length) (ha : G.Adj a (p.getVert n)) : n < 13 := by
    by_contra hge
    exact hnone ⟨n, by omega, hn, ha⟩
  have index_exists (z : G.neighborSet a) :
      ∃ n : ℕ, p.getVert n = z.val ∧ n < 13 ∧ n % 2 = 1 := by
    have hz := maximal_path_neighbor_mem p hp hmax z.property
    obtain ⟨n, hnz, hn⟩ := Walk.mem_support_iff_exists_getVert.mp hz
    have ha : G.Adj a (p.getVert n) := hnz.symm ▸ z.property
    exact ⟨n, hnz, hsmall n hn ha, adjacent_path_index_odd c p n hn ha⟩
  let index : G.neighborSet a → ℕ := fun z => Classical.choose (index_exists z)
  have hi (z : G.neighborSet a) :
      p.getVert (index z) = z.val ∧ index z < 13 ∧ index z % 2 = 1 :=
    Classical.choose_spec (index_exists z)
  let rank : G.neighborSet a → Fin 6 := fun z => ⟨index z / 2, by
    have hz := hi z
    omega⟩
  have hrank : Function.Injective rank := by
    intro z w heq
    have hv : index z / 2 = index w / 2 := congrArg Fin.val heq
    have hz := hi z
    have hw := hi w
    have hidx : index z = index w := by omega
    apply Subtype.ext
    calc
      z.val = p.getVert (index z) := hz.1.symm
      _ = p.getVert (index w) := congrArg p.getVert hidx
      _ = w.val := hw.1
  have hcard := Fintype.card_le_of_injective rank hrank
  have hdeg : G.degree a ≤ 6 := by
    simpa only [Fintype.card_fin, G.card_neighborSet_eq_degree] using hcard
  omega

theorem path_closing_cycle {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hab : G.Adj a b) (hlen : 2 ≤ p.length) :
    (Walk.cons hab.symm p).IsCycle := by
  apply (Walk.cons_isCycle_iff p hab.symm).mpr
  refine ⟨hp, ?_⟩
  intro he
  have he' : s(a, b) ∈ p.edges := by simpa only [Sym2.eq_swap] using he
  have h := hp.length_eq_one_of_mem_edges he'
  omega

theorem exists_cycle_length_ge_fourteen [Fintype V] [Nonempty V]
    (hb : G.IsBipartite) (hd : ∀ a : V, 7 ≤ G.degree a) :
    ∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ 14 ≤ p.length := by
  classical
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  obtain ⟨a, b, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  obtain ⟨n, hn, hle, hadj⟩ := maximal_path_far_neighbor c p hp hmax (hd a)
  have hlen : (p.take n).length = n := by
    simp only [Walk.take_length, inf_eq_left.mpr hle]
  refine ⟨p.getVert n, Walk.cons hadj.symm (p.take n), ?_, ?_⟩
  · exact path_closing_cycle (p.take n) (hp.take n) hadj (by omega)
  · simp only [Walk.length_cons, hlen]
    omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.maximal_path_neighbor_mem
#print axioms TaskH.Seven.BP.adjacent_path_index_odd
#print axioms TaskH.Seven.BP.maximal_path_far_neighbor
#print axioms TaskH.Seven.BP.path_closing_cycle
#print axioms TaskH.Seven.BP.exists_cycle_length_ge_fourteen
