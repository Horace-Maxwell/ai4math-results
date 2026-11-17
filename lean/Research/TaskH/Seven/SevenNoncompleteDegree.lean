import Research.TaskH.Seven.SevenDegreeSeven
import Research.TaskH.Degree

/-!
The first actual noncomplete branch has degree at least eight and order at
least nine. These internal graph conclusions support the separate capacity4
prefix; they do not assume the existence of a minimum-degree vertex.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem critical_seven_card_ge_eight (hcrit : IsCriticalPlus 7 G) :
    8 ≤ Fintype.card V := by
  have h : (8 : ℕ∞) ≤ (Fintype.card V : ℕ∞) := by
    have h := G.chromaticNumber_le_card
    rw [hcrit.1] at h
    exact h
  exact_mod_cast h

theorem noncomplete_degree_ge_eight (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V) : 8 ≤ G.degree v := by
  have hd := critical_degree_ge hcrit v
  have hne : G.degree v ≠ 7 := fun he => hnot (degreeSeven_isCompleteOfOrder hcrit hs hr v he)
  omega

theorem noncomplete_card_ge_nine (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hnot : ¬ IsCompleteOfOrder G 8) : 9 ≤ Fintype.card V := by
  classical
  have hn := critical_seven_card_ge_eight hcrit
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice inferInstance
  have hd := noncomplete_degree_ge_eight hcrit hs hr hnot v
  have hlt := G.degree_lt_card_verts v
  omega

end TaskH.Seven

#print axioms TaskH.Seven.critical_seven_card_ge_eight
#print axioms TaskH.Seven.noncomplete_degree_ge_eight
#print axioms TaskH.Seven.noncomplete_card_ge_nine
