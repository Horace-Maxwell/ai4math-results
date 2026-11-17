import Research.TaskH.Five.FivePatternForcedColors

/-! Exact internal degrees and external attachment sums on actual pattern vertices. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

def PatternExactEmbedding (G : SimpleGraph V) (P : Finset (Sym2 (Fin 5)))
    (f : Fin 5 → V) : Prop :=
  PatternEmbedding G P f ∧ ∀ i j, G.Adj (f i) (f j) → s(i, j) ∈ P

variable [Fintype V] [DecidableRel G.Adj]

theorem pattern_internal_degree {P : Finset (Sym2 (Fin 5))} {f : Fin 5 → V}
    (hf : PatternExactEmbedding G P f) (i : Fin 5) :
    (neighborsIn G (patternVertexSet f) (f i)).card =
      ((Finset.univ : Finset (Fin 5)).filter (fun j => s(i, j) ∈ P)).card := by
  rw [patternNeighborIndices_card hf.1]
  congr 1
  ext j
  simp only [patternNeighborIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hf.2 i j, hf.1.2 i j⟩

theorem pattern_internal_degree_sum {P : Finset (Sym2 (Fin 5))} {f : Fin 5 → V}
    (hf : PatternExactEmbedding G P f) :
    (∑ v ∈ patternVertexSet f, (neighborsIn G (patternVertexSet f) v).card) =
      ∑ i : Fin 5, ((Finset.univ : Finset (Fin 5)).filter (fun j => s(i, j) ∈ P)).card := by
  rw [patternVertexSet, Finset.sum_image hf.1.1.injOn]
  exact Finset.sum_congr rfl (fun i _ => pattern_internal_degree hf i)

theorem star_internal_degree_sum {f : Fin 5 → V}
    (hf : PatternExactEmbedding G patternStar f) :
    (∑ v ∈ patternVertexSet f, (neighborsIn G (patternVertexSet f) v).card) = 16 := by
  rw [pattern_internal_degree_sum hf]
  decide +kernel

theorem gem_internal_degree_sum {f : Fin 5 → V}
    (hf : PatternExactEmbedding G patternGem f) :
    (∑ v ∈ patternVertexSet f, (neighborsIn G (patternVertexSet f) v).card) = 14 := by
  rw [pattern_internal_degree_sum hf]
  decide +kernel

theorem star_anchor_internal_degree {f : Fin 5 → V}
    (hf : PatternExactEmbedding G patternStar f) :
    (neighborsIn G (patternVertexSet f) (f 4)).card = 2 := by
  rw [pattern_internal_degree hf]
  decide +kernel

theorem gem_left_anchor_internal_degree {f : Fin 5 → V}
    (hf : PatternExactEmbedding G patternGem f) :
    (neighborsIn G (patternVertexSet f) (f 0)).card = 2 := by
  rw [pattern_internal_degree hf]
  decide +kernel

theorem gem_right_anchor_internal_degree {f : Fin 5 → V}
    (hf : PatternExactEmbedding G patternGem f) :
    (neighborsIn G (patternVertexSet f) (f 3)).card = 2 := by
  rw [pattern_internal_degree hf]
  decide +kernel

theorem pattern_external_degree_sum_bound {P : Finset (Sym2 (Fin 5))}
    {f : Fin 5 → V} (hf : PatternEmbedding G P f)
    (hout : ∀ v ∈ (patternVertexSet f)ᶜ,
      (neighborsIn G (patternVertexSet f) v).card ≤ 2) :
    (∑ v ∈ (patternVertexSet f)ᶜ, (neighborsIn G (patternVertexSet f) v).card) ≤
      (patternVertexSet f)ᶜ.card + (doubleOuterVertices G f).card := by
  classical
  let S := patternVertexSet f
  let R := doubleOuterVertices G f
  have hrow : ∀ v ∈ Sᶜ, (neighborsIn G S v).card ≤
      1 + if (neighborsIn G S v).card = 2 then 1 else 0 := by
    intro v hv
    have hh := hout v hv
    change (neighborsIn G S v).card ≤ 2 at hh
    by_cases he : (neighborsIn G S v).card = 2
    · rw [ite_eq_left he]
      omega
    · rw [ite_eq_right he]
      omega
  have he : (Sᶜ.filter (fun v => (neighborsIn G S v).card = 2)) = R := by
    ext v
    simp only [R, doubleOuterVertices, Finset.mem_filter]
    rw [patternNeighborIndices_card hf]
  calc
    _ ≤ ∑ v ∈ Sᶜ, (1 + if (neighborsIn G S v).card = 2 then 1 else 0) :=
      Finset.sum_le_sum hrow
    _ = Sᶜ.card + ∑ v ∈ Sᶜ, if (neighborsIn G S v).card = 2 then 1 else 0 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one]
    _ = Sᶜ.card + (Sᶜ.filter (fun v => (neighborsIn G S v).card = 2)).card := by
      congr 1
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = _ := by rw [he]

theorem pattern_total_degree_sum_bound {P : Finset (Sym2 (Fin 5))}
    {f : Fin 5 → V} (hf : PatternEmbedding G P f)
    (hout : ∀ v ∈ (patternVertexSet f)ᶜ,
      (neighborsIn G (patternVertexSet f) v).card ≤ 2)
    (I : ℕ) (hin : (∑ v ∈ patternVertexSet f,
      (neighborsIn G (patternVertexSet f) v).card) ≤ I) :
    (∑ v ∈ patternVertexSet f, G.degree v) ≤
      I + (patternVertexSet f)ᶜ.card + (doubleOuterVertices G f).card := by
  rw [sum_degrees_on_set]
  have hh := pattern_external_degree_sum_bound hf hout
  omega

end TaskH.Five

#print axioms TaskH.Five.pattern_internal_degree
#print axioms TaskH.Five.pattern_internal_degree_sum
#print axioms TaskH.Five.star_internal_degree_sum
#print axioms TaskH.Five.gem_internal_degree_sum
#print axioms TaskH.Five.star_anchor_internal_degree
#print axioms TaskH.Five.gem_left_anchor_internal_degree
#print axioms TaskH.Five.gem_right_anchor_internal_degree
#print axioms TaskH.Five.pattern_external_degree_sum_bound
#print axioms TaskH.Five.pattern_total_degree_sum_bound
