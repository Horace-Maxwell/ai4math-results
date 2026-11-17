import Research.TaskH.Seven.SevenBPChordWitnessData

/-! Every forbidden pattern is transported to a true original-graph C14. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem forbidden_E1 (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (i : Fin 16) :
    ¬ (FiveChord G u i ∧ FiveChord G u (i + 2)) := by
  rintro ⟨h0, h1⟩
  have hreq : ∀ a b : Fin 16, s(a, b) ∈ requiredE1 →
      G.Adj (u (i + a)) (u (i + b)) := by
    intro a b hab
    simp only [requiredE1, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with he0 | he1
    · apply adj_of_rotated_edge_eq u i 0 5 a b ?_ he0
      simpa only [FiveChord, add_zero] using h0
    · apply adj_of_rotated_edge_eq u i 2 7 a b ?_ he1
      simpa only [FiveChord, add_assoc, show (2 : Fin 16) + 5 = 7 by decide] using h1
  obtain ⟨x, p, hp, hl⟩ := exists_fourteen_cycle_of_rotated_word u hu i
    requiredE1 wordE1 wordE1_valid hreq
  exact hn p hp hl

theorem forbidden_E2 (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (i : Fin 16) :
    ¬ (FiveChord G u i ∧ FiveChord G u (i + 1) ∧ FiveChord G u (i + 4)) := by
  rintro ⟨h0, h1, h2⟩
  have hreq : ∀ a b : Fin 16, s(a, b) ∈ requiredE2 →
      G.Adj (u (i + a)) (u (i + b)) := by
    intro a b hab
    simp only [requiredE2, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with he0 | he1 | he2
    · apply adj_of_rotated_edge_eq u i 0 5 a b ?_ he0
      simpa only [FiveChord, add_zero] using h0
    · apply adj_of_rotated_edge_eq u i 1 6 a b ?_ he1
      simpa only [FiveChord, add_assoc, show (1 : Fin 16) + 5 = 6 by decide] using h1
    · apply adj_of_rotated_edge_eq u i 4 9 a b ?_ he2
      simpa only [FiveChord, add_assoc, show (4 : Fin 16) + 5 = 9 by decide] using h2
  obtain ⟨x, p, hp, hl⟩ := exists_fourteen_cycle_of_rotated_word u hu i
    requiredE2 wordE2 wordE2_valid hreq
  exact hn p hp hl

theorem forbidden_F1a (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (i : Fin 16) :
    ¬ (SevenChord G u i ∧ SevenChord G u (i + 2)) := by
  rintro ⟨h0, h1⟩
  have hreq : ∀ a b : Fin 16, s(a, b) ∈ requiredF1a →
      G.Adj (u (i + a)) (u (i + b)) := by
    intro a b hab
    simp only [requiredF1a, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with he0 | he1
    · apply adj_of_rotated_edge_eq u i 0 7 a b ?_ he0
      simpa only [SevenChord, add_zero] using h0
    · apply adj_of_rotated_edge_eq u i 2 9 a b ?_ he1
      simpa only [SevenChord, add_assoc, show (2 : Fin 16) + 7 = 9 by decide] using h1
  obtain ⟨x, p, hp, hl⟩ := exists_fourteen_cycle_of_rotated_word u hu i
    requiredF1a wordF1a wordF1a_valid hreq
  exact hn p hp hl

theorem forbidden_F1b (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (i : Fin 16) :
    ¬ (SevenChord G u i ∧ SevenChord G u (i + 6)) := by
  rintro ⟨h0, h1⟩
  have hreq : ∀ a b : Fin 16, s(a, b) ∈ requiredF1b →
      G.Adj (u (i + a)) (u (i + b)) := by
    intro a b hab
    simp only [requiredF1b, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with he0 | he1
    · apply adj_of_rotated_edge_eq u i 0 7 a b ?_ he0
      simpa only [SevenChord, add_zero] using h0
    · apply adj_of_rotated_edge_eq u i 6 13 a b ?_ he1
      simpa only [SevenChord, add_assoc, show (6 : Fin 16) + 7 = 13 by decide] using h1
  obtain ⟨x, p, hp, hl⟩ := exists_fourteen_cycle_of_rotated_word u hu i
    requiredF1b wordF1b wordF1b_valid hreq
  exact hn p hp hl

theorem forbidden_M1a (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (i : Fin 16) :
    ¬ (FiveChord G u i ∧ SevenChord G u (i + 1)) := by
  rintro ⟨h0, h1⟩
  have hreq : ∀ a b : Fin 16, s(a, b) ∈ requiredM1a →
      G.Adj (u (i + a)) (u (i + b)) := by
    intro a b hab
    simp only [requiredM1a, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with he0 | he1
    · apply adj_of_rotated_edge_eq u i 0 5 a b ?_ he0
      simpa only [FiveChord, add_zero] using h0
    · apply adj_of_rotated_edge_eq u i 1 8 a b ?_ he1
      simpa only [SevenChord, add_assoc, show (1 : Fin 16) + 7 = 8 by decide] using h1
  obtain ⟨x, p, hp, hl⟩ := exists_fourteen_cycle_of_rotated_word u hu i
    requiredM1a wordM1a wordM1a_valid hreq
  exact hn p hp hl

theorem forbidden_M1b (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (i : Fin 16) :
    ¬ (FiveChord G u i ∧ SevenChord G u (i + 13)) := by
  rintro ⟨h0, h1⟩
  have hreq : ∀ a b : Fin 16, s(a, b) ∈ requiredM1b →
      G.Adj (u (i + a)) (u (i + b)) := by
    intro a b hab
    simp only [requiredM1b, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with he0 | he1
    · apply adj_of_rotated_edge_eq u i 0 5 a b ?_ he0
      simpa only [FiveChord, add_zero] using h0
    · apply adj_of_rotated_edge_eq u i 13 4 a b ?_ he1
      simpa only [SevenChord, add_assoc, show (13 : Fin 16) + 7 = 4 by decide] using h1
  obtain ⟨x, p, hp, hl⟩ := exists_fourteen_cycle_of_rotated_word u hu i
    requiredM1b wordM1b wordM1b_valid hreq
  exact hn p hp hl

theorem forbidden_M2a (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (i : Fin 16) :
    ¬ (SevenChord G u i ∧ SevenChord G u (i + 1) ∧ FiveChord G u (i + 5)) := by
  rintro ⟨h0, h1, h2⟩
  have hreq : ∀ a b : Fin 16, s(a, b) ∈ requiredM2a →
      G.Adj (u (i + a)) (u (i + b)) := by
    intro a b hab
    simp only [requiredM2a, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with he0 | he1 | he2
    · apply adj_of_rotated_edge_eq u i 0 7 a b ?_ he0
      simpa only [SevenChord, add_zero] using h0
    · apply adj_of_rotated_edge_eq u i 1 8 a b ?_ he1
      simpa only [SevenChord, add_assoc, show (1 : Fin 16) + 7 = 8 by decide] using h1
    · apply adj_of_rotated_edge_eq u i 5 10 a b ?_ he2
      simpa only [FiveChord, add_assoc, show (5 : Fin 16) + 5 = 10 by decide] using h2
  obtain ⟨x, p, hp, hl⟩ := exists_fourteen_cycle_of_rotated_word u hu i
    requiredM2a wordM2a wordM2a_valid hreq
  exact hn p hp hl

theorem forbidden_M2b (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (i : Fin 16) :
    ¬ (SevenChord G u i ∧ SevenChord G u (i + 1) ∧ FiveChord G u (i + 6)) := by
  rintro ⟨h0, h1, h2⟩
  have hreq : ∀ a b : Fin 16, s(a, b) ∈ requiredM2b →
      G.Adj (u (i + a)) (u (i + b)) := by
    intro a b hab
    simp only [requiredM2b, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with he0 | he1 | he2
    · apply adj_of_rotated_edge_eq u i 0 7 a b ?_ he0
      simpa only [SevenChord, add_zero] using h0
    · apply adj_of_rotated_edge_eq u i 1 8 a b ?_ he1
      simpa only [SevenChord, add_assoc, show (1 : Fin 16) + 7 = 8 by decide] using h1
    · apply adj_of_rotated_edge_eq u i 6 11 a b ?_ he2
      simpa only [FiveChord, add_assoc, show (6 : Fin 16) + 5 = 11 by decide] using h2
  obtain ⟨x, p, hp, hl⟩ := exists_fourteen_cycle_of_rotated_word u hu i
    requiredM2b wordM2b wordM2b_valid hreq
  exact hn p hp hl

theorem forbidden_M2c (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (i : Fin 16) :
    ¬ (SevenChord G u i ∧ SevenChord G u (i + 1) ∧ FiveChord G u (i + 13)) := by
  rintro ⟨h0, h1, h2⟩
  have hreq : ∀ a b : Fin 16, s(a, b) ∈ requiredM2c →
      G.Adj (u (i + a)) (u (i + b)) := by
    intro a b hab
    simp only [requiredM2c, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with he0 | he1 | he2
    · apply adj_of_rotated_edge_eq u i 0 7 a b ?_ he0
      simpa only [SevenChord, add_zero] using h0
    · apply adj_of_rotated_edge_eq u i 1 8 a b ?_ he1
      simpa only [SevenChord, add_assoc, show (1 : Fin 16) + 7 = 8 by decide] using h1
    · apply adj_of_rotated_edge_eq u i 13 2 a b ?_ he2
      simpa only [FiveChord, add_assoc, show (13 : Fin 16) + 5 = 2 by decide] using h2
  obtain ⟨x, p, hp, hl⟩ := exists_fourteen_cycle_of_rotated_word u hu i
    requiredM2c wordM2c wordM2c_valid hreq
  exact hn p hp hl

theorem forbidden_M2d (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (i : Fin 16) :
    ¬ (SevenChord G u i ∧ SevenChord G u (i + 1) ∧ FiveChord G u (i + 14)) := by
  rintro ⟨h0, h1, h2⟩
  have hreq : ∀ a b : Fin 16, s(a, b) ∈ requiredM2d →
      G.Adj (u (i + a)) (u (i + b)) := by
    intro a b hab
    simp only [requiredM2d, Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with he0 | he1 | he2
    · apply adj_of_rotated_edge_eq u i 0 7 a b ?_ he0
      simpa only [SevenChord, add_zero] using h0
    · apply adj_of_rotated_edge_eq u i 1 8 a b ?_ he1
      simpa only [SevenChord, add_assoc, show (1 : Fin 16) + 7 = 8 by decide] using h1
    · apply adj_of_rotated_edge_eq u i 14 3 a b ?_ he2
      simpa only [FiveChord, add_assoc, show (14 : Fin 16) + 5 = 3 by decide] using h2
  obtain ⟨x, p, hp, hl⟩ := exists_fourteen_cycle_of_rotated_word u hu i
    requiredM2d wordM2d wordM2d_valid hreq
  exact hn p hp hl

noncomputable def fiveChordIndices (G : SimpleGraph V) (u : Fin 16 → V) : Finset (Fin 16) := by
  classical
  exact Finset.univ.filter (FiveChord G u)

noncomputable def sevenChordIndices (G : SimpleGraph V) (u : Fin 16 → V) : Finset (Fin 16) := by
  classical
  exact Finset.univ.filter (SevenChord G u)

theorem mem_fiveChordIndices (u : Fin 16 → V) (i : Fin 16) :
    i ∈ fiveChordIndices G u ↔ FiveChord G u i := by
  classical
  simp only [fiveChordIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_sevenChordIndices (u : Fin 16 → V) (i : Fin 16) :
    i ∈ sevenChordIndices G u ↔ SevenChord G u i := by
  classical
  simp only [sevenChordIndices, Finset.mem_filter, Finset.mem_univ, true_and]

def ChordRestrictions (E F : Finset (Fin 16)) : Prop :=
  (∀ i, i ∈ E → i + 2 ∉ E) ∧
  (∀ i, i ∈ E → i + 1 ∈ E → i + 4 ∉ E) ∧
  (∀ i, i ∈ F → i + 2 ∉ F ∧ i + 6 ∉ F) ∧
  (∀ i, i ∈ E → i + 1 ∉ F ∧ i + 13 ∉ F) ∧
  (∀ i, i ∈ F → i + 1 ∈ F →
    i + 5 ∉ E ∧ i + 6 ∉ E ∧ i + 13 ∉ E ∧ i + 14 ∉ E)

theorem actual_chord_restrictions (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) :
    ChordRestrictions (fiveChordIndices G u) (sevenChordIndices G u) := by
  classical
  simp only [ChordRestrictions, mem_fiveChordIndices, mem_sevenChordIndices]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i h0 h2
    exact forbidden_E1 u hu hn i ⟨h0, h2⟩
  · intro i h0 h1 h4
    exact forbidden_E2 u hu hn i ⟨h0, h1, h4⟩
  · intro i h0
    exact ⟨fun h2 => forbidden_F1a u hu hn i ⟨h0, h2⟩,
      fun h6 => forbidden_F1b u hu hn i ⟨h0, h6⟩⟩
  · intro i h0
    exact ⟨fun h1 => forbidden_M1a u hu hn i ⟨h0, h1⟩,
      fun h13 => forbidden_M1b u hu hn i ⟨h0, h13⟩⟩
  · intro i h0 h1
    exact ⟨fun h5 => forbidden_M2a u hu hn i ⟨h0, h1, h5⟩,
      fun h6 => forbidden_M2b u hu hn i ⟨h0, h1, h6⟩,
      fun h13 => forbidden_M2c u hu hn i ⟨h0, h1, h13⟩,
      fun h14 => forbidden_M2d u hu hn i ⟨h0, h1, h14⟩⟩

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.forbidden_E1
#print axioms TaskH.Seven.BP.forbidden_E2
#print axioms TaskH.Seven.BP.forbidden_F1a
#print axioms TaskH.Seven.BP.forbidden_F1b
#print axioms TaskH.Seven.BP.forbidden_M1a
#print axioms TaskH.Seven.BP.forbidden_M1b
#print axioms TaskH.Seven.BP.forbidden_M2a
#print axioms TaskH.Seven.BP.forbidden_M2b
#print axioms TaskH.Seven.BP.forbidden_M2c
#print axioms TaskH.Seven.BP.forbidden_M2d
#print axioms TaskH.Seven.BP.fiveChordIndices
#print axioms TaskH.Seven.BP.sevenChordIndices
#print axioms TaskH.Seven.BP.mem_fiveChordIndices
#print axioms TaskH.Seven.BP.mem_sevenChordIndices
#print axioms TaskH.Seven.BP.ChordRestrictions
#print axioms TaskH.Seven.BP.actual_chord_restrictions
