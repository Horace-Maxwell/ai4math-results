import Research.TaskH.Five.FiveRigidityData
import Research.TaskH.Five.FivePatternDegree

/-! Missing-edge rigidity is transported to the actual five embedded vertices. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

theorem pattern_embedding_of_extra_reindex
    {P Q : Finset (Sym2 (Fin 5))} {f : Fin 5 → V}
    (hf : PatternEmbedding G P f) (i j : Fin 5) (hij : G.Adj (f i) (f j))
    (r : Fin 5 → Fin 5) (hr : Function.Injective r)
    (hmap : ∀ a b : Fin 5, s(a, b) ∈ Q → s(r a, r b) ∈ insert s(i, j) P) :
    PatternEmbedding G Q (f ∘ r) := by
  refine ⟨hf.1.comp hr, ?_⟩
  intro a b hab
  rcases Finset.mem_insert.mp (hmap a b hab) with he | hm
  · rcases Sym2.eq_iff.mp he with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simpa only [Function.comp_apply, ha, hb] using hij
    · simpa only [Function.comp_apply, ha, hb] using hij.symm
  · exact hf.2 (r a) (r b) hm

theorem star_embedding_exact {f : Fin 5 → V}
    (hf : PatternEmbedding G patternStar f)
    (hnear : ∀ r : Fin 5 → V, ¬ PatternEmbedding G patternNearComplete r) :
    PatternExactEmbedding G patternStar f := by
  refine ⟨hf, ?_⟩
  intro i j hij
  by_contra hex
  have hne : i ≠ j := fun he => hij.ne (congrArg f he)
  obtain ⟨r, hr, hmap⟩ := star_extra_reindex i j hne hex
  exact hnear (f ∘ r) (pattern_embedding_of_extra_reindex hf i j hij r hr hmap)

theorem gem_embedding_exact {f : Fin 5 → V}
    (hf : PatternEmbedding G patternGem f)
    (hmatching : ∀ r : Fin 5 → V, ¬ PatternEmbedding G patternMissingMatching r)
    (hstar : ∀ r : Fin 5 → V, ¬ PatternEmbedding G patternStar r) :
    PatternExactEmbedding G patternGem f := by
  refine ⟨hf, ?_⟩
  intro i j hij
  by_contra hex
  have hne : i ≠ j := fun he => hij.ne (congrArg f he)
  rcases gem_extra_reindex i j hne hex with ⟨r, hr, hmap⟩ | ⟨r, hr, hmap⟩
  · exact hmatching (f ∘ r)
      (pattern_embedding_of_extra_reindex hf i j hij r hr hmap)
  · exact hstar (f ∘ r)
      (pattern_embedding_of_extra_reindex hf i j hij r hr hmap)

end TaskH.Five

#print axioms TaskH.Five.pattern_embedding_of_extra_reindex
#print axioms TaskH.Five.star_embedding_exact
#print axioms TaskH.Five.gem_embedding_exact
