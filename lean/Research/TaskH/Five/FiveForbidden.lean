import Research.TaskH.Five.FiveGroupBounds
import Research.TaskH.Five.FiveForbiddenBudget
import Research.TaskH.Five.FiveHighDegree

/-! Actual graph star and gem exclusion; every auxiliary attachment bound is discharged. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem no_star_pattern
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hn9 : 9 ≤ Fintype.card V) (hn22 : Fintype.card V ≤ 22)
    (h13 : ∀ v : V, 13 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard)
    (hdeg : ∀ v : V, 6 ≤ G.degree v) :
    ∀ f : Fin 5 → V, ¬ PatternEmbedding G patternStar f := by
  intro f hf
  have hnear := no_nearComplete_pattern hcrit hs hr hc hn9 h13 hsingle
  have he := star_embedding_exact hf hnear
  exact no_star_of_doubleOuter_bound hcrit hs hr hc (by omega) h13 hsingle he
    (star_doubleOuter_card_le_two hcrit hr hn9 hn22 hdeg he)

theorem no_gem_pattern
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hn9 : 9 ≤ Fintype.card V) (hn22 : Fintype.card V ≤ 22)
    (h13 : ∀ v : V, 13 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard)
    (hdeg : ∀ v : V, 6 ≤ G.degree v) :
    ∀ f : Fin 5 → V, ¬ PatternEmbedding G patternGem f := by
  intro f hf
  have hmatching := no_missingMatching_pattern hcrit hs hr hc hn9 h13 hsingle
  have hstar := no_star_pattern hcrit hs hr hc hn9 hn22 h13 hsingle hdeg
  have he := gem_embedding_exact hf hmatching hstar
  exact no_gem_of_doubleOuter_bound hcrit hs hr hc (by omega) h13 hsingle he
    (gem_doubleOuter_card_le_four hcrit hr hn9 hn22 hdeg he)

theorem no_gem_pattern_of_high_minDegree
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hdeg : ∀ v : V, 6 ≤ G.degree v)
    (hE : ∀ {x y : V}, G.Adj x y →
      12 ≤ (TaskH.modCyclesThroughAvoid 5 G x y).ncard)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard) :
    ∀ f : Fin 5 → V, ¬ PatternEmbedding G patternGem f := by
  exact no_gem_pattern hcrit hs hr hc
    (nine_le_card_of_high_minDegree hcrit hs hr hc hdeg hE hsingle)
    (card_le_twenty_two_of_high_minDegree hcrit hs hr hc hdeg hE hsingle)
    (thirteen_le_cycleDegree hcrit hE) hsingle hdeg

end TaskH.Five

#print axioms TaskH.Five.no_star_pattern
#print axioms TaskH.Five.no_gem_pattern
#print axioms TaskH.Five.no_gem_pattern_of_high_minDegree
