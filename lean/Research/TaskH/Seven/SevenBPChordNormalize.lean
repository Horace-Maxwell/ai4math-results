import Research.TaskH.Seven.SevenBPChordResidues

/-! Seven-chord support concentration and a genuine cyclic choice of origin.
Only index identities over two Fin4 positions are kernel checked. -/

set_option autoImplicit false

namespace TaskH.Seven.BP

def chordOrigin (a : Fin 4) : Fin 16 := ⟨a.val, by omega⟩

theorem seven_chord_opposite_groups (E F : Finset (Fin 16))
    (h : ChordRestrictions E F) (o : Fin 16) (r : Fin 4) (hr : r = 0 ∨ r = 1) :
    chordResidueGroup F o r = ∅ ∨ chordResidueGroup F o (r + 2) = ∅ := by
  classical
  by_cases hempty : chordResidueGroup F o r = ∅
  · exact Or.inl hempty
  · right
    obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hft := (mem_chordResidueGroup F o r t).mp ht
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hfs := (mem_chordResidueGroup F o (r + 2) s).mp hs
    have tab : ∀ r t s : Fin 4, r = 0 ∨ r = 1 →
        chordGroupIndex (r + 2) s = chordGroupIndex r t + 2 ∨
        chordGroupIndex (r + 2) s = chordGroupIndex r t + 6 ∨
        chordGroupIndex r t = chordGroupIndex (r + 2) s + 2 ∨
        chordGroupIndex r t = chordGroupIndex (r + 2) s + 6 := by decide +kernel
    rcases tab r t s hr with he | he | he | he
    · exact (h.2.2.1 _ hft).1 (by simpa only [add_assoc, ← he] using hfs)
    · exact (h.2.2.1 _ hft).2 (by simpa only [add_assoc, ← he] using hfs)
    · exact (h.2.2.1 _ hfs).1 (by simpa only [add_assoc, ← he] using hft)
    · exact (h.2.2.1 _ hfs).2 (by simpa only [add_assoc, ← he] using hft)

theorem chord_residue_empty_of_shift (F : Finset (Fin 16)) (a r : Fin 4)
    (h : chordResidueGroup F 0 (r + a) = ∅) :
    chordResidueGroup F (chordOrigin a) r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have tab : ∀ a r t : Fin 4, ∃ s : Fin 4,
      chordOrigin a + chordGroupIndex r t = chordGroupIndex (r + a) s := by decide +kernel
  obtain ⟨s, hs⟩ := tab a r t
  have hf : s ∈ chordResidueGroup F 0 (r + a) := by
    apply (mem_chordResidueGroup F 0 (r + a) s).mpr
    simpa only [zero_add, ← hs] using (mem_chordResidueGroup F (chordOrigin a) r t).mp ht
  rw [h] at hf
  exact Finset.notMem_empty s hf

theorem seven_chord_normalized_origin (E F : Finset (Fin 16))
    (h : ChordRestrictions E F) :
    ∃ o : Fin 16, chordResidueGroup F o 2 = ∅ ∧ chordResidueGroup F o 3 = ∅ := by
  have heven : chordResidueGroup F 0 0 = ∅ ∨ chordResidueGroup F 0 2 = ∅ := by
    simpa only [show (0 : Fin 4) + 2 = 2 by decide] using
      seven_chord_opposite_groups E F h 0 0 (Or.inl rfl)
  have hodd : chordResidueGroup F 0 1 = ∅ ∨ chordResidueGroup F 0 3 = ∅ := by
    simpa only [show (1 : Fin 4) + 2 = 3 by decide] using
      seven_chord_opposite_groups E F h 0 1 (Or.inr rfl)
  rcases heven with h0 | h2
  · rcases hodd with h1 | h3
    · exact ⟨chordOrigin 2, chord_residue_empty_of_shift F 2 2
          (by simpa only [show (2 : Fin 4) + 2 = 0 by decide] using h0),
        chord_residue_empty_of_shift F 2 3
          (by simpa only [show (3 : Fin 4) + 2 = 1 by decide] using h1)⟩
    · exact ⟨chordOrigin 1, chord_residue_empty_of_shift F 1 2
          (by simpa only [show (2 : Fin 4) + 1 = 3 by decide] using h3),
        chord_residue_empty_of_shift F 1 3
          (by simpa only [show (3 : Fin 4) + 1 = 0 by decide] using h0)⟩
  · rcases hodd with h1 | h3
    · exact ⟨chordOrigin 3, chord_residue_empty_of_shift F 3 2
          (by simpa only [show (2 : Fin 4) + 3 = 1 by decide] using h1),
        chord_residue_empty_of_shift F 3 3
          (by simpa only [show (3 : Fin 4) + 3 = 2 by decide] using h2)⟩
    · exact ⟨0, h2, h3⟩

theorem normalized_seven_chord_card (F : Finset (Fin 16)) (o : Fin 16)
    (h2 : chordResidueGroup F o 2 = ∅) (h3 : chordResidueGroup F o 3 = ∅) :
    F.card = (chordResidueGroup F o 0).card + (chordResidueGroup F o 1).card := by
  have hh := chord_residue_card_partition F o
  simpa only [h2, h3, Finset.card_empty, Nat.add_zero] using hh

theorem sevenChordIndices_card_le_eight_of_restrictions (E F : Finset (Fin 16))
    (h : ChordRestrictions E F) : F.card ≤ 8 := by
  obtain ⟨o, h2, h3⟩ := seven_chord_normalized_origin E F h
  have hcard := normalized_seven_chord_card F o h2 h3
  have h0 : (chordResidueGroup F o 0).card ≤ 4 := by
    simpa using Finset.card_le_univ (chordResidueGroup F o 0)
  have h1 : (chordResidueGroup F o 1).card ≤ 4 := by
    simpa using Finset.card_le_univ (chordResidueGroup F o 1)
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.chordOrigin
#print axioms TaskH.Seven.BP.seven_chord_opposite_groups
#print axioms TaskH.Seven.BP.chord_residue_empty_of_shift
#print axioms TaskH.Seven.BP.seven_chord_normalized_origin
#print axioms TaskH.Seven.BP.normalized_seven_chord_card
#print axioms TaskH.Seven.BP.sevenChordIndices_card_le_eight_of_restrictions
