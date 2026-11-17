import Research.TaskH.Five.CycleFive

/-!
Four literal five-position edge patterns and their finite path tables.
Only kernel-checked finite identities occur here. Transport into an actual
graph, deleted-vertex colorings, and rainbow cycles is in a separate module.
-/

set_option autoImplicit false

namespace TaskH.Five

open SimpleGraph

/-- The complete five-position graph with just the edge `01` removed. -/
def patternNearComplete : Finset (Sym2 (Fin 5)) :=
  {s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 3), s(1, 4),
    s(2, 3), s(2, 4), s(3, 4)}

/-- The complete five-position graph with the disjoint edges `01,23` removed. -/
def patternMissingMatching : Finset (Sym2 (Fin 5)) :=
  {s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 3), s(1, 4),
    s(2, 4), s(3, 4)}

/-- Positions `0,1,2,3` form a clique; position `4` is joined just to `0,1`. -/
def patternStar : Finset (Sym2 (Fin 5)) :=
  {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3),
    s(0, 4), s(1, 4)}

/-- The gem: hub `4` joined to the path `0-1-2-3`. -/
def patternGem : Finset (Sym2 (Fin 5)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(0, 4), s(1, 4), s(2, 4), s(3, 4)}

/-- A literal three-edge simple path in a five-position edge pattern. -/
def PatternThreePath (P : Finset (Sym2 (Fin 5))) (t : Fin 4 → Fin 5) : Prop :=
  Function.Injective t ∧ s(t 0, t 1) ∈ P ∧ s(t 1, t 2) ∈ P ∧ s(t 2, t 3) ∈ P

/-- The necessary condition supplied by the rainbow obstruction when the
outside point has color anchor `q` and neighbor-position set `A`. -/
def PatternNoThreePath (P : Finset (Sym2 (Fin 5))) (q : Fin 5)
    (A : Finset (Fin 5)) : Prop :=
  ∀ t : Fin 4 → Fin 5, PatternThreePath P t → t 0 ∈ A → t 3 ∈ A →
    ∀ j : Fin 4, t j ≠ q

/-- A finite five-position Hamilton cycle, with the five edges exposed in
the same order as `IsPentagon`. -/
def PatternHamilton (P : Finset (Sym2 (Fin 5))) (h : Fin 5 → Fin 5) : Prop :=
  Function.Injective h ∧ s(h 0, h 1) ∈ P ∧ s(h 1, h 2) ∈ P ∧
    s(h 2, h 3) ∈ P ∧ s(h 3, h 4) ∈ P ∧ s(h 4, h 0) ∈ P

def patternNearCompleteHamilton : Fin 5 → Fin 5 := ![0, 2, 1, 3, 4]

def patternMissingMatchingHamilton : Fin 5 → Fin 5 := ![0, 2, 1, 3, 4]

def patternStarHamilton : Fin 5 → Fin 5 := ![4, 0, 2, 3, 1]

def patternGemHamilton : Fin 5 → Fin 5 := ![4, 0, 1, 2, 3]

theorem patternNearComplete_card : patternNearComplete.card = 9 := by
  decide +kernel

theorem patternMissingMatching_card : patternMissingMatching.card = 8 := by
  decide +kernel

theorem patternStar_card : patternStar.card = 8 := by
  decide +kernel

theorem patternGem_card : patternGem.card = 7 := by
  decide +kernel

theorem patternNearComplete_hamilton :
    PatternHamilton patternNearComplete patternNearCompleteHamilton := by
  unfold PatternHamilton Function.Injective
  decide +kernel

theorem patternMissingMatching_hamilton :
    PatternHamilton patternMissingMatching patternMissingMatchingHamilton := by
  unfold PatternHamilton Function.Injective
  decide +kernel

theorem patternStar_hamilton : PatternHamilton patternStar patternStarHamilton := by
  unfold PatternHamilton Function.Injective
  decide +kernel

theorem patternGem_hamilton : PatternHamilton patternGem patternGemHamilton := by
  unfold PatternHamilton Function.Injective
  decide +kernel

theorem nearComplete_no_attachment (q : Fin 5) (A : Finset (Fin 5))
    (hq : q ∉ A) (hcard : A.card = 2)
    (hno : PatternNoThreePath patternNearComplete q A) : False := by
  revert q A
  unfold PatternNoThreePath PatternThreePath Function.Injective
  decide +kernel

theorem missingMatching_no_attachment (q : Fin 5) (A : Finset (Fin 5))
    (hq : q ∉ A) (hcard : A.card = 2)
    (hno : PatternNoThreePath patternMissingMatching q A) : False := by
  revert q A
  unfold PatternNoThreePath PatternThreePath Function.Injective
  decide +kernel

theorem star_attachment_table (q : Fin 5) (A : Finset (Fin 5))
    (hq : q ∉ A) (hcard : A.card = 2)
    (hno : PatternNoThreePath patternStar q A) :
    q = 4 ∧ (A = {0, 1} ∨ A = {2, 3}) := by
  obtain ⟨a, b, hab, hA⟩ := Finset.card_eq_two.mp hcard
  subst A
  fin_cases q <;> fin_cases a <;> fin_cases b
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![1, 0, 3, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![1, 0, 2, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![1, 2, 0, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![2, 0, 3, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![2, 0, 1, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![2, 0, 1, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![3, 0, 2, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![3, 0, 1, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![3, 0, 1, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![4, 0, 2, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![4, 0, 1, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![4, 0, 1, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![0, 1, 3, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![0, 1, 2, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![0, 2, 1, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![2, 1, 3, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![2, 0, 1, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![2, 0, 1, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![3, 1, 2, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![3, 0, 1, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![3, 0, 1, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![4, 1, 2, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![4, 0, 1, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![4, 0, 1, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![0, 2, 3, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![0, 1, 2, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![0, 2, 1, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![1, 2, 3, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![1, 0, 2, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![1, 2, 0, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![3, 1, 2, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![3, 0, 2, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![3, 2, 0, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![4, 1, 2, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![4, 0, 2, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![4, 0, 2, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![0, 2, 3, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![0, 1, 3, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![0, 3, 1, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![1, 2, 3, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![1, 0, 3, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![1, 3, 0, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![2, 1, 3, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![2, 0, 3, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![2, 3, 0, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![4, 1, 3, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![4, 0, 3, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![4, 0, 3, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · decide +kernel
  · exact False.elim ((hno ![0, 4, 1, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![0, 4, 1, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · decide +kernel
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![1, 4, 0, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![1, 4, 0, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![2, 1, 4, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![2, 0, 4, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hab (by decide +kernel))
  · decide +kernel
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![3, 1, 4, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![3, 0, 4, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · decide +kernel
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))

theorem gem_attachment_table (q : Fin 5) (A : Finset (Fin 5))
    (hq : q ∉ A) (hcard : A.card = 2)
    (hno : PatternNoThreePath patternGem q A) :
    (q = 0 ∧ (A = {4, 1} ∨ A = {4, 3} ∨ A = {2, 3})) ∨
      (q = 3 ∧ (A = {4, 2} ∨ A = {4, 0} ∨ A = {0, 1})) := by
  obtain ⟨a, b, hab, hA⟩ := Finset.card_eq_two.mp hcard
  subst A
  fin_cases q <;> fin_cases a <;> fin_cases b
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![1, 0, 4, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![1, 0, 4, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · decide +kernel
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![2, 4, 0, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hab (by decide +kernel))
  · decide +kernel
  · exact False.elim ((hno ![2, 1, 0, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![3, 4, 0, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · decide +kernel
  · exact False.elim (hab (by decide +kernel))
  · decide +kernel
  · exact False.elim (hq (by decide +kernel))
  · decide +kernel
  · exact False.elim ((hno ![4, 0, 1, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · decide +kernel
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![0, 1, 4, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![0, 1, 2, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![0, 1, 2, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![2, 1, 4, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![2, 1, 4, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![2, 1, 0, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![3, 2, 1, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![3, 4, 1, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![3, 2, 1, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![4, 2, 1, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![4, 0, 1, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![4, 1, 2, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![0, 4, 2, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![0, 1, 2, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![0, 1, 2, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![1, 2, 4, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![1, 2, 4, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![1, 2, 3, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![3, 2, 1, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![3, 2, 4, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![3, 2, 1, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![4, 2, 1, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![4, 3, 2, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![4, 1, 2, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · decide +kernel
  · exact False.elim ((hno ![0, 4, 3, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · decide +kernel
  · decide +kernel
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![1, 4, 3, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![1, 2, 3, 4] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![2, 3, 4, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![2, 3, 4, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · decide +kernel
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · decide +kernel
  · exact False.elim ((hno ![4, 3, 2, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · decide +kernel
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![0, 4, 2, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim ((hno ![0, 1, 4, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![0, 1, 4, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![1, 2, 4, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![1, 0, 4, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![1, 0, 4, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![2, 1, 4, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![2, 3, 4, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim ((hno ![2, 1, 4, 3] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim ((hno ![3, 2, 4, 0] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![3, 2, 4, 1] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      2) rfl)
  · exact False.elim ((hno ![3, 4, 1, 2] (by
      unfold PatternThreePath Function.Injective
      decide +kernel) (by decide +kernel) (by decide +kernel)
      1) rfl)
  · exact False.elim (hab (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hq (by decide +kernel))
  · exact False.elim (hab (by decide +kernel))

end TaskH.Five

#print axioms TaskH.Five.patternNearComplete_card
#print axioms TaskH.Five.patternMissingMatching_card
#print axioms TaskH.Five.patternStar_card
#print axioms TaskH.Five.patternGem_card
#print axioms TaskH.Five.patternNearComplete_hamilton
#print axioms TaskH.Five.patternMissingMatching_hamilton
#print axioms TaskH.Five.patternStar_hamilton
#print axioms TaskH.Five.patternGem_hamilton
#print axioms TaskH.Five.nearComplete_no_attachment
#print axioms TaskH.Five.missingMatching_no_attachment
#print axioms TaskH.Five.star_attachment_table
#print axioms TaskH.Five.gem_attachment_table
