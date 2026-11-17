import Research.TaskH.Seven.SevenBPChordBudget

/-! Actual bipartite-cycle parity and the missing distance-three chord
obstruction. The latter constructs a genuine fourteen-cycle. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

def chordCycleSixteenWalk (G : SimpleGraph V) (u : Fin 16 → V)
    (ha : ∀ i : Fin 16, G.Adj (u i) (u (i + 1))) : G.Walk (u 0) (u 0) :=
  (.cons (ha 0) (.cons (ha 1) (.cons (ha 2) (.cons (ha 3) (.cons (ha 4) (.cons (ha 5) (.cons (ha 6) (.cons (ha 7) (.cons (ha 8) (.cons (ha 9) (.cons (ha 10) (.cons (ha 11) (.cons (ha 12) (.cons (ha 13) (.cons (ha 14) (.cons (ha 15) .nil))))))))))))))))

theorem chordCycleSixteenWalk_length (G : SimpleGraph V) (u : Fin 16 → V)
    (ha : ∀ i : Fin 16, G.Adj (u i) (u (i + 1))) :
    (chordCycleSixteenWalk G u ha).length = 16 := rfl

theorem chordCycleSixteenWalk_getVert (G : SimpleGraph V) (u : Fin 16 → V)
    (ha : ∀ i : Fin 16, G.Adj (u i) (u (i + 1))) (i : Fin 16) :
    (chordCycleSixteenWalk G u ha).getVert i.val = u i := by
  fin_cases i <;> rfl

theorem cycle_sixteen_color_even_iff (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (c : G.Coloring Bool) (i : Fin 16) :
    Even i.val ↔ (c (u 0) ↔ c (u i)) := by
  have hh := c.even_length_iff_congr ((chordCycleSixteenWalk G u hu.2).take i.val)
  simpa only [Walk.take_length, chordCycleSixteenWalk_length,
    inf_eq_left.mpr (Nat.le_of_lt i.isLt), chordCycleSixteenWalk_getVert] using hh

theorem cycle_sixteen_adj_parity_ne (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (c : G.Coloring Bool) (i j : Fin 16) (ha : G.Adj (u i) (u j)) :
    i.val % 2 ≠ j.val % 2 := by
  intro he
  have hi := cycle_sixteen_color_even_iff u hu c i
  have hj := cycle_sixteen_color_even_iff u hu c j
  have hs : Even i.val ↔ Even j.val := by
    rw [Nat.even_iff, Nat.even_iff, he]
  have hn := c.valid ha
  cases h0 : c (u 0) <;> cases h1 : c (u i) <;> cases h2 : c (u j) <;> simp_all

def requiredThreeChord : Finset (Sym2 (Fin 16)) := {s(0, 3)}

def wordThreeChord : Fin 14 → Fin 16 := ![0,3,4,5,6,7,8,9,10,11,12,13,14,15]

theorem wordThreeChord_valid : WordValid requiredThreeChord wordThreeChord := by
  unfold WordValid requiredThreeChord wordThreeChord Function.Injective
  decide +kernel

theorem no_three_chord (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (i : Fin 16) : ¬ G.Adj (u i) (u (i + 3)) := by
  intro h3
  have hreq : ∀ a b : Fin 16, s(a, b) ∈ requiredThreeChord →
      G.Adj (u (i + a)) (u (i + b)) := by
    intro a b hab
    have he : s(a, b) = s(0, 3) := Finset.mem_singleton.mp hab
    apply adj_of_rotated_edge_eq u i 0 3 a b ?_ he
    simpa only [add_zero] using h3
  obtain ⟨x, p, hp, hl⟩ := exists_fourteen_cycle_of_rotated_word u hu i
    requiredThreeChord wordThreeChord wordThreeChord_valid hreq
  exact hn p hp hl

theorem noncycle_adj_is_five_or_seven (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (c : G.Coloring Bool) (i j : Fin 16)
    (ha : G.Adj (u i) (u j)) (hn1 : j ≠ i + 1) (hp1 : i ≠ j + 1) :
    j = i + 5 ∨ i = j + 5 ∨ j = i + 7 ∨ i = j + 7 := by
  have hpar := cycle_sixteen_adj_parity_ne u hu c i j ha
  have hn3 : j ≠ i + 3 := by
    intro he
    exact no_three_chord u hu hn i (he ▸ ha)
  have hp3 : i ≠ j + 3 := by
    intro he
    exact no_three_chord u hu hn j (he ▸ ha.symm)
  have tab : ∀ i j : Fin 16, i.val % 2 ≠ j.val % 2 →
      j ≠ i + 1 → i ≠ j + 1 → j ≠ i + 3 → i ≠ j + 3 →
      j = i + 5 ∨ i = j + 5 ∨ j = i + 7 ∨ i = j + 7 := by decide +kernel
  exact tab i j hpar hn1 hp1 hn3 hp3

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.chordCycleSixteenWalk
#print axioms TaskH.Seven.BP.chordCycleSixteenWalk_length
#print axioms TaskH.Seven.BP.chordCycleSixteenWalk_getVert
#print axioms TaskH.Seven.BP.cycle_sixteen_color_even_iff
#print axioms TaskH.Seven.BP.cycle_sixteen_adj_parity_ne
#print axioms TaskH.Seven.BP.requiredThreeChord
#print axioms TaskH.Seven.BP.wordThreeChord
#print axioms TaskH.Seven.BP.wordThreeChord_valid
#print axioms TaskH.Seven.BP.no_three_chord
#print axioms TaskH.Seven.BP.noncycle_adj_is_five_or_seven
