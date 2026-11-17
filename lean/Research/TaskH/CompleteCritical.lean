import Research.TaskH.Critical

set_option autoImplicit false

universe u

namespace TaskH

open SimpleGraph Challenge

/-- Merging a nonadjacent pair saves one color. This is also the construction
in Mathlib's `eq_top_of_chromaticNumber_eq_card` proof. -/
theorem colorable_card_sub_one_of_ne_top {V : Type u} [Fintype V]
    (G : SimpleGraph V) (h : G ≠ ⊤) : G.Colorable (Fintype.card V - 1) := by
  classical
  obtain ⟨a, b, hne, hab⟩ := SimpleGraph.ne_top_iff_exists_not_adj.mp h
  suffices C : G.Coloring ((Finset.univ : Finset V).erase b) from by
    simpa using C.colorable
  apply SimpleGraph.Coloring.mk
    (fun x => if hx : x ≠ b then ⟨x, by simp [hx]⟩ else ⟨a, by simp [hne]⟩)
  grind [SimpleGraph.Adj.ne', SimpleGraph.adj_symm]

theorem complete_isCriticalPlus (k : ℕ) :
    IsCriticalPlus k (⊤ : SimpleGraph (Fin (k + 1))) := by
  classical
  constructor
  · simp [SimpleGraph.chromaticNumber_top]
  · intro S hproper
    let : Fintype S.verts := Fintype.ofFinite _
    by_cases hsmall : Fintype.card S.verts ≤ k
    · exact (SimpleGraph.colorable_of_fintype S.coe).mono hsmall
    · have hle : Fintype.card S.verts ≤ k + 1 := by
        simpa only [Fintype.card_fin] using Fintype.card_subtype_le (· ∈ S.verts)
      have hcard : Fintype.card S.verts = k + 1 := by omega
      have hverts : S.verts = Set.univ :=
        (set_fintype_card_eq_univ_iff S.verts).mp (by simpa only [Fintype.card_fin] using hcard)
      have hcoe : S.coe ≠ ⊤ := by
        intro htop
        apply hproper
        apply SimpleGraph.Subgraph.ext hverts
        funext x y
        apply propext
        constructor
        · intro hxy
          exact S.adj_sub hxy
        · intro hxy
          have hx : x ∈ S.verts := by rw [hverts]; trivial
          have hy : y ∈ S.verts := by rw [hverts]; trivial
          have hne : (⟨x, hx⟩ : S.verts) ≠ ⟨y, hy⟩ := by
            intro heq
            exact hxy (congrArg Subtype.val heq)
          have ha : S.coe.Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
            rw [htop]
            exact hne
          exact ha
      have hc := colorable_card_sub_one_of_ne_top S.coe hcoe
      simpa only [hcard, Nat.add_sub_cancel] using hc

#print axioms colorable_card_sub_one_of_ne_top
#print axioms complete_isCriticalPlus

end TaskH
