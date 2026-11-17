import Research.TaskH.Five.FiveForcedGroupPaths
import Research.TaskH.Five.FivePatternDegree

/-! Insert the actual anchor into an external forced-color class. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

noncomputable def attachedGroup (f : Fin 5 → V) (a : Fin 5) (R : Finset V) : Finset V :=
  insert (f a) R

variable [Fintype V]

theorem attachedGroup_card (f : Fin 5 → V) (a : Fin 5) (R : Finset V)
    (hR : R ⊆ (patternVertexSet f)ᶜ) : (attachedGroup f a R).card = R.card + 1 := by
  have ha : f a ∈ patternVertexSet f :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hnot : f a ∉ R := fun h => (Finset.mem_compl.mp (hR h)) ha
  exact Finset.card_insert_of_notMem hnot

theorem attachedGroup_inter (f : Fin 5 → V) (a : Fin 5) (R : Finset V)
    (hR : R ⊆ (patternVertexSet f)ᶜ) :
    (patternVertexSet f ∩ attachedGroup f a R).card = 1 := by
  have ha : f a ∈ patternVertexSet f :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have he : patternVertexSet f ∩ attachedGroup f a R = {f a} := by
    ext x
    constructor
    · intro hx
      have hs := (Finset.mem_inter.mp hx).1
      have hz := (Finset.mem_inter.mp hx).2
      rcases Finset.mem_insert.mp hz with he | hm
      · exact Finset.mem_singleton.mpr he
      · exact False.elim ((Finset.mem_compl.mp (hR hm)) hs)
    · intro hx
      have he := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_inter.mpr ⟨ha, Finset.mem_insert_self _ _⟩
  rw [he, Finset.card_singleton]

omit [Fintype V] in
theorem attachedGroup_forced (f : Fin 5 → V) (a : Fin 5) (R : Finset V)
    (hforce : ∀ x ∈ R, ForcedTo G f a x) :
    ∀ x ∈ attachedGroup f a R, ForcedTo G f a x := by
  intro x hx
  rcases Finset.mem_insert.mp hx with he | hm
  · subst x
    exact anchor_forcedTo f a
  · exact hforce x hm

variable [DecidableRel G.Adj]

theorem attachedGroup_card_le_two
    (hcrit : Challenge.IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    (hn9 : 9 ≤ Fintype.card V) (hn22 : Fintype.card V ≤ 22)
    (f : Fin 5 → V) (a : Fin 5) (R : Finset V)
    (hS : (patternVertexSet f).card = 5)
    (hR : R ⊆ (patternVertexSet f)ᶜ)
    (hforce : ∀ x ∈ R, ForcedTo G f a x)
    (hdeg : ∀ x : V, 6 ≤ G.degree x)
    (hanchor : (neighborsIn G (patternVertexSet f) (f a)).card ≤ 2)
    (hin : ∀ x ∈ R, (neighborsIn G (patternVertexSet f) x).card ≤ 2)
    (hcross : ∀ x ∈ attachedGroup f a R, ∀ y ∈ attachedGroup f a R, x ≠ y →
      ∃ i j : Fin 5, G.Adj x (f i) ∧ G.Adj (f i) (f j) ∧ G.Adj (f j) y) :
    R.card ≤ 2 := by
  let Z := attachedGroup f a R
  have hforceZ := attachedGroup_forced f a R hforce
  have hinZ : ∀ x ∈ Z, (neighborsIn G (patternVertexSet f) x).card ≤ 2 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hm
    · simpa only [he] using hanchor
    · exact hin x hm
  have hcommon := forced_group_common_neighbors_unique hcrit hr hn9 f a Z hforceZ hcross
  have hb := forced_group_four_neighbors_budget hcrit hn9 f a Z hS
    (attachedGroup_inter f a R hR) hforceZ hdeg hinZ hcommon
  have hzcard := attachedGroup_card f a R hR
  change 5 * (attachedGroup f a R).card + 4 ≤ Fintype.card V at hb
  rw [hzcard] at hb
  omega

end TaskH.Five

#print axioms TaskH.Five.attachedGroup_card
#print axioms TaskH.Five.attachedGroup_inter
#print axioms TaskH.Five.attachedGroup_forced
#print axioms TaskH.Five.attachedGroup_card_le_two
