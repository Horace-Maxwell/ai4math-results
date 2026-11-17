import Research.TaskH.Five.FivePatternDegree

/-! The actual singleton and incidence budgets exclude the bounded star and gem attachments. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem no_pattern_of_internal_and_doubleOuter_budget
    (hs : ShortFiveCycles G) (hc : modCycleCount 5 G = 72)
    (h13 : ∀ v : V, 13 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard)
    {P : Finset (Sym2 (Fin 5))} {f : Fin 5 → V}
    (hf : PatternEmbedding G P f)
    (hout : ∀ v ∈ (patternVertexSet f)ᶜ,
      (neighborsIn G (patternVertexSet f) v).card ≤ 2)
    (I R : ℕ)
    (hin : (∑ v ∈ patternVertexSet f,
      (neighborsIn G (patternVertexSet f) v).card) ≤ I)
    (hR : (doubleOuterVertices G f).card ≤ R)
    (hIR : I + R ≤ 18) : False := by
  have hdegree := pattern_total_degree_sum_bound hf hout I hin
  have hD : (∑ v ∈ patternVertexSet f, G.degree v) ≤
      (patternVertexSet f)ᶜ.card + 18 := by omega
  have hbudget := five_set_incidence_degree_budget hs hc h13 hsingle
    (patternVertexSet f) (patternVertexSet_card hf)
    ((patternVertexSet f)ᶜ.card + 18) hD
  omega

theorem no_star_of_doubleOuter_bound
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hn7 : 7 ≤ Fintype.card V)
    (h13 : ∀ v : V, 13 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard)
    {f : Fin 5 → V} (hf : PatternExactEmbedding G patternStar f)
    (hR : (doubleOuterVertices G f).card ≤ 2) : False := by
  apply no_pattern_of_internal_and_doubleOuter_budget hs hc h13 hsingle hf.1
    (fun y hy => ?_) 16 2 (by rw [star_internal_degree_sum hf]) hR (by decide)
  rw [patternNeighborIndices_card hf.1]
  exact pattern_outer_neighbors_le_two hcrit hr hn7 hf.1 patternStar_hamilton
    y (Finset.mem_compl.mp hy)

theorem no_gem_of_doubleOuter_bound
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hn7 : 7 ≤ Fintype.card V)
    (h13 : ∀ v : V, 13 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard)
    {f : Fin 5 → V} (hf : PatternExactEmbedding G patternGem f)
    (hR : (doubleOuterVertices G f).card ≤ 4) : False := by
  apply no_pattern_of_internal_and_doubleOuter_budget hs hc h13 hsingle hf.1
    (fun y hy => ?_) 14 4 (by rw [gem_internal_degree_sum hf]) hR (by decide)
  rw [patternNeighborIndices_card hf.1]
  exact pattern_outer_neighbors_le_two hcrit hr hn7 hf.1 patternGem_hamilton
    y (Finset.mem_compl.mp hy)

end TaskH.Five

#print axioms TaskH.Five.no_pattern_of_internal_and_doubleOuter_budget
#print axioms TaskH.Five.no_star_of_doubleOuter_bound
#print axioms TaskH.Five.no_gem_of_doubleOuter_bound
