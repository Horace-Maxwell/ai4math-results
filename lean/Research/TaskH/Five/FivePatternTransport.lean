import Research.TaskH.Five.FivePatternData
import Research.TaskH.Five.FiveAttachment
import Research.TaskH.Five.FiveSetBudget

/-! Transport literal five-position paths into the actual graph and coloring. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

def PatternEmbedding (G : SimpleGraph V) (P : Finset (Sym2 (Fin 5)))
    (f : Fin 5 → V) : Prop :=
  Function.Injective f ∧ ∀ i j, s(i, j) ∈ P → G.Adj (f i) (f j)

noncomputable def patternVertexSet (f : Fin 5 → V) : Finset V :=
  Finset.univ.image f

noncomputable def patternNeighborIndices (G : SimpleGraph V) (f : Fin 5 → V)
    (y : V) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => G.Adj y (f i))

theorem patternVertexSet_card {P : Finset (Sym2 (Fin 5))} {f : Fin 5 → V}
    (hf : PatternEmbedding G P f) : (patternVertexSet f).card = 5 := by
  rw [patternVertexSet, Finset.card_image_of_injective _ hf.1,
    Finset.card_univ, Fintype.card_fin]

theorem patternHamilton_isPentagon {P : Finset (Sym2 (Fin 5))}
    {f : Fin 5 → V} {h : Fin 5 → Fin 5}
    (hf : PatternEmbedding G P f) (hh : PatternHamilton P h) :
    IsPentagon G (f ∘ h) := by
  exact ⟨hf.1.comp hh.1, hf.2 _ _ hh.2.1, hf.2 _ _ hh.2.2.1,
    hf.2 _ _ hh.2.2.2.1, hf.2 _ _ hh.2.2.2.2.1, hf.2 _ _ hh.2.2.2.2.2⟩

theorem pattern_coloring_injective {P : Finset (Sym2 (Fin 5))}
    {f : Fin 5 → V} {h : Fin 5 → Fin 5}
    (hr : RainbowFiveCycles G) (hf : PatternEmbedding G P f)
    (hh : PatternHamilton P h) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 5)) (hfw : ∀ i, f i ≠ w) :
    Function.Injective (fun i => c ⟨f i, hfw i⟩) := by
  let g := f ∘ h
  have hg : IsPentagon G g := patternHamilton_isPentagon hf hh
  let p := pentagonWalk G g hg.2.1 hg.2.2.1 hg.2.2.2.1
    hg.2.2.2.2.1 hg.2.2.2.2.2
  have hp : p.IsCycle := pentagonWalk_isCycle G g hg.1 hg.2.1 hg.2.2.1
    hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2
  have hfin : ∀ i, f i ∈ p.support := by
    intro i
    obtain ⟨j, hj⟩ := Finite.surjective_of_injective hh.1 i
    rw [← hj]
    change g j ∈ p.support
    fin_cases j <;> simp [p, pentagonWalk, Walk.support_cons]
  intro i j hij
  apply hf.1
  have he := hr w c p hp (by rfl) ⟨f i, hfw i⟩ ⟨f j, hfw j⟩
    (hfin i) (hfin j) hij
  exact congrArg Subtype.val he

theorem pattern_noThreePath_of_color {P : Finset (Sym2 (Fin 5))}
    {f : Fin 5 → V} (hr : RainbowFiveCycles G) (hf : PatternEmbedding G P f)
    (w : V) (c : (G.induce {x | x ≠ w}).Coloring (Fin 5))
    (hfw : ∀ i, f i ≠ w) (y : V) (hyw : y ≠ w)
    (hyout : ∀ i, y ≠ f i) (q : Fin 5)
    (hq : c ⟨y, hyw⟩ = c ⟨f q, hfw q⟩) :
    PatternNoThreePath P q (patternNeighborIndices G f y) := by
  intro t ht h0 h3 j hj
  let r := f ∘ t
  have hrinj : Function.Injective r := hf.1.comp ht.1
  have hrw : ∀ i, r i ≠ w := fun i => hfw (t i)
  have hyout' : ∀ i, y ≠ r i := fun i => hyout (t i)
  have hc : c ⟨y, hyw⟩ = c ⟨r j, hrw j⟩ := by
    simpa only [r, Function.comp_apply, hj] using hq
  have hnot := rainbow_forbids_three_path hr w c r hrinj
    (hf.2 _ _ ht.2.1) (hf.2 _ _ ht.2.2.1) (hf.2 _ _ ht.2.2.2)
    y hyw hrw hyout' j hc
  exact hnot ⟨(Finset.mem_filter.mp h0).2, (Finset.mem_filter.mp h3).2⟩

theorem pattern_coloring_attachment_constraints {P : Finset (Sym2 (Fin 5))}
    {f : Fin 5 → V} {h : Fin 5 → Fin 5}
    (hr : RainbowFiveCycles G) (hf : PatternEmbedding G P f)
    (hh : PatternHamilton P h) (w : V)
    (c : (G.induce {x | x ≠ w}).Coloring (Fin 5)) (hfw : ∀ i, f i ≠ w)
    (y : V) (hyw : y ≠ w) (hyout : ∀ i, y ≠ f i) :
    ∃ q : Fin 5, c ⟨y, hyw⟩ = c ⟨f q, hfw q⟩ ∧
      q ∉ patternNeighborIndices G f y ∧
      PatternNoThreePath P q (patternNeighborIndices G f y) := by
  have hinj := pattern_coloring_injective hr hf hh w c hfw
  obtain ⟨q, hq⟩ := Finite.surjective_of_injective hinj (c ⟨y, hyw⟩)
  have hcolor : c ⟨y, hyw⟩ = c ⟨f q, hfw q⟩ := hq.symm
  refine ⟨q, hcolor, ?_, pattern_noThreePath_of_color hr hf w c hfw y hyw hyout q hcolor⟩
  intro hmem
  have ha : (G.induce {x | x ≠ w}).Adj ⟨y, hyw⟩ ⟨f q, hfw q⟩ :=
    (Finset.mem_filter.mp hmem).2
  exact (c.valid ha) hcolor

theorem patternNeighborIndices_image [Fintype V] [DecidableRel G.Adj]
    (f : Fin 5 → V) (y : V) :
    neighborsIn G (patternVertexSet f) y = (patternNeighborIndices G f y).image f := by
  ext x
  simp only [neighborsIn, patternNeighborIndices, Finset.mem_filter,
    patternVertexSet, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, rfl⟩, hyi⟩
    exact ⟨i, hyi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, rfl⟩, hi⟩

theorem patternNeighborIndices_card [Fintype V] [DecidableRel G.Adj]
    {P : Finset (Sym2 (Fin 5))} {f : Fin 5 → V} (hf : PatternEmbedding G P f)
    (y : V) :
    (neighborsIn G (patternVertexSet f) y).card =
      (patternNeighborIndices G f y).card := by
  rw [patternNeighborIndices_image f, Finset.card_image_of_injective _ hf.1]

end TaskH.Five

#print axioms TaskH.Five.patternVertexSet_card
#print axioms TaskH.Five.patternHamilton_isPentagon
#print axioms TaskH.Five.pattern_coloring_injective
#print axioms TaskH.Five.pattern_noThreePath_of_color
#print axioms TaskH.Five.pattern_coloring_attachment_constraints
#print axioms TaskH.Five.patternNeighborIndices_image
#print axioms TaskH.Five.patternNeighborIndices_card
