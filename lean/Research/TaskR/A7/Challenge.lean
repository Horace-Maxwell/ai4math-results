import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.Fintype.Fin

namespace TaskR.A7.Challenge

abbrev G := alternatingGroup (Fin 7)

/-- The left quotient of two successive vertices of the ordered path. -/
def difference (a : Fin 2520 → G) (i : Fin 2519) : G :=
  (a i.castSucc)⁻¹ * a i.succ

/-- An ordinary terrace counts occurrences in inverse pairs. A nonidentity
involution occurs once, and each other nonidentity inverse pair occurs twice. -/
def HasTerrace : Prop :=
  ∃ a : Fin 2520 ≃ G, a 0 = 1 ∧
    ∀ g : G, g ≠ 1 →
      Fintype.card {i : Fin 2519 // difference a i = g ∨ difference a i = g⁻¹} =
        if g = g⁻¹ then 1 else 2

end TaskR.A7.Challenge
