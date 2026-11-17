import Research.TaskH.Seven.SevenBPCycleWitness

/-! The ten literal fourteen-index sequences handwritten in BP45-C16-07.
Finite proofs only certify those ten sequences; no graph enumeration occurs. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph

def WordValid (E : Finset (Sym2 (Fin 16))) (w : Fin 14 → Fin 16) : Prop :=
  Function.Injective w ∧ ∀ j : Fin 14,
    w j + 1 = w (j + 1) ∨ w (j + 1) + 1 = w j ∨ s(w j, w (j + 1)) ∈ E

def requiredE1 : Finset (Sym2 (Fin 16)) :=
  {s(0, 5), s(2, 7)}

def wordE1 : Fin 14 → Fin 16 :=
  ![0, 5, 4, 3, 2, 7, 8, 9, 10, 11, 12, 13, 14, 15]

theorem wordE1_valid : WordValid requiredE1 wordE1 := by
  unfold WordValid requiredE1 wordE1 Function.Injective
  decide +kernel

def requiredE2 : Finset (Sym2 (Fin 16)) :=
  {s(0, 5), s(1, 6), s(4, 9)}

def wordE2 : Fin 14 → Fin 16 :=
  ![0, 5, 6, 1, 2, 3, 4, 9, 10, 11, 12, 13, 14, 15]

theorem wordE2_valid : WordValid requiredE2 wordE2 := by
  unfold WordValid requiredE2 wordE2 Function.Injective
  decide +kernel

def requiredF1a : Finset (Sym2 (Fin 16)) :=
  {s(0, 7), s(2, 9)}

def wordF1a : Fin 14 → Fin 16 :=
  ![0, 7, 6, 5, 4, 3, 2, 9, 10, 11, 12, 13, 14, 15]

theorem wordF1a_valid : WordValid requiredF1a wordF1a := by
  unfold WordValid requiredF1a wordF1a Function.Injective
  decide +kernel

def requiredF1b : Finset (Sym2 (Fin 16)) :=
  {s(0, 7), s(6, 13)}

def wordF1b : Fin 14 → Fin 16 :=
  ![0, 1, 2, 3, 4, 5, 6, 13, 12, 11, 10, 9, 8, 7]

theorem wordF1b_valid : WordValid requiredF1b wordF1b := by
  unfold WordValid requiredF1b wordF1b Function.Injective
  decide +kernel

def requiredM1a : Finset (Sym2 (Fin 16)) :=
  {s(0, 5), s(1, 8)}

def wordM1a : Fin 14 → Fin 16 :=
  ![0, 5, 4, 3, 2, 1, 8, 9, 10, 11, 12, 13, 14, 15]

theorem wordM1a_valid : WordValid requiredM1a wordM1a := by
  unfold WordValid requiredM1a wordM1a Function.Injective
  decide +kernel

def requiredM1b : Finset (Sym2 (Fin 16)) :=
  {s(0, 5), s(13, 4)}

def wordM1b : Fin 14 → Fin 16 :=
  ![0, 1, 2, 3, 4, 13, 12, 11, 10, 9, 8, 7, 6, 5]

theorem wordM1b_valid : WordValid requiredM1b wordM1b := by
  unfold WordValid requiredM1b wordM1b Function.Injective
  decide +kernel

def requiredM2a : Finset (Sym2 (Fin 16)) :=
  {s(0, 7), s(1, 8), s(5, 10)}

def wordM2a : Fin 14 → Fin 16 :=
  ![5, 10, 11, 12, 13, 14, 15, 0, 7, 8, 1, 2, 3, 4]

theorem wordM2a_valid : WordValid requiredM2a wordM2a := by
  unfold WordValid requiredM2a wordM2a Function.Injective
  decide +kernel

def requiredM2b : Finset (Sym2 (Fin 16)) :=
  {s(0, 7), s(1, 8), s(6, 11)}

def wordM2b : Fin 14 → Fin 16 :=
  ![6, 11, 12, 13, 14, 15, 0, 7, 8, 1, 2, 3, 4, 5]

theorem wordM2b_valid : WordValid requiredM2b wordM2b := by
  unfold WordValid requiredM2b wordM2b Function.Injective
  decide +kernel

def requiredM2c : Finset (Sym2 (Fin 16)) :=
  {s(0, 7), s(1, 8), s(13, 2)}

def wordM2c : Fin 14 → Fin 16 :=
  ![13, 2, 3, 4, 5, 6, 7, 0, 1, 8, 9, 10, 11, 12]

theorem wordM2c_valid : WordValid requiredM2c wordM2c := by
  unfold WordValid requiredM2c wordM2c Function.Injective
  decide +kernel

def requiredM2d : Finset (Sym2 (Fin 16)) :=
  {s(0, 7), s(1, 8), s(14, 3)}

def wordM2d : Fin 14 → Fin 16 :=
  ![14, 3, 4, 5, 6, 7, 0, 1, 8, 9, 10, 11, 12, 13]

theorem wordM2d_valid : WordValid requiredM2d wordM2d := by
  unfold WordValid requiredM2d wordM2d Function.Injective
  decide +kernel

variable {V : Type u} {G : SimpleGraph V}

theorem exists_fourteen_cycle_of_rotated_word (u : Fin 16 → V)
    (hu : IsCycleSixteen G u) (i : Fin 16)
    (E : Finset (Sym2 (Fin 16))) (w : Fin 14 → Fin 16) (hw : WordValid E w)
    (hE : ∀ a b : Fin 16, s(a, b) ∈ E → G.Adj (u (i + a)) (u (i + b))) :
    ∃ x : V, ∃ p : G.Walk x x, p.IsCycle ∧ p.length = 14 := by
  let f : Fin 14 → V := fun j => u (i + w j)
  have hf : Function.Injective f := by
    intro j k he
    exact hw.1 (add_left_cancel (hu.1 he))
  have ha : ∀ j : Fin 14, G.Adj (f j) (f (j + 1)) := by
    intro j
    change G.Adj (u (i + w j)) (u (i + w (j + 1)))
    rcases hw.2 j with hnext | hprev | hedge
    · have hh := hu.2 (i + w j)
      simpa only [add_assoc, hnext] using hh
    · have hh := (hu.2 (i + w (j + 1))).symm
      simpa only [add_assoc, hprev] using hh
    · exact hE (w j) (w (j + 1)) hedge
  exact exists_fourteen_cycle_of_injective_adj G f hf ha

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.WordValid
#print axioms TaskH.Seven.BP.requiredE1
#print axioms TaskH.Seven.BP.wordE1
#print axioms TaskH.Seven.BP.wordE1_valid
#print axioms TaskH.Seven.BP.requiredE2
#print axioms TaskH.Seven.BP.wordE2
#print axioms TaskH.Seven.BP.wordE2_valid
#print axioms TaskH.Seven.BP.requiredF1a
#print axioms TaskH.Seven.BP.wordF1a
#print axioms TaskH.Seven.BP.wordF1a_valid
#print axioms TaskH.Seven.BP.requiredF1b
#print axioms TaskH.Seven.BP.wordF1b
#print axioms TaskH.Seven.BP.wordF1b_valid
#print axioms TaskH.Seven.BP.requiredM1a
#print axioms TaskH.Seven.BP.wordM1a
#print axioms TaskH.Seven.BP.wordM1a_valid
#print axioms TaskH.Seven.BP.requiredM1b
#print axioms TaskH.Seven.BP.wordM1b
#print axioms TaskH.Seven.BP.wordM1b_valid
#print axioms TaskH.Seven.BP.requiredM2a
#print axioms TaskH.Seven.BP.wordM2a
#print axioms TaskH.Seven.BP.wordM2a_valid
#print axioms TaskH.Seven.BP.requiredM2b
#print axioms TaskH.Seven.BP.wordM2b
#print axioms TaskH.Seven.BP.wordM2b_valid
#print axioms TaskH.Seven.BP.requiredM2c
#print axioms TaskH.Seven.BP.wordM2c
#print axioms TaskH.Seven.BP.wordM2c_valid
#print axioms TaskH.Seven.BP.requiredM2d
#print axioms TaskH.Seven.BP.wordM2d
#print axioms TaskH.Seven.BP.wordM2d_valid
#print axioms TaskH.Seven.BP.exists_fourteen_cycle_of_rotated_word
