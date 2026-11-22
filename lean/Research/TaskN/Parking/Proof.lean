import Research.TaskN.Parking.ParkClassification
import Research.TaskN.Parking.SpacingCount

namespace TaskN.Parking.Proof
open Challenge
open scoped Classical

private theorem positive_of_dominant {xs : List ℕ} (h : dominant xs) : positive xs := by
  induction xs with
  | nil => simp [positive]
  | cons x xs ih =>
    change xs.sum < x ∧ dominant xs at h
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hr
    · omega
    · exact ih h.2 v hr

theorem ExtremalClassification : Challenge.ExtremalClassification := classification

theorem FirstLengthCount : Challenge.FirstLengthCount := by
  intro b xs hd
  have hbd : xs.sum < b ∧ dominant xs := hd
  rw [← arithmetic_count b xs hbd.2]
  congr 1
  ext a
  simp only [Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨hband,he⟩
    have hp : positive (a::b::xs) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hh
      · omega
      · exact positive_of_dominant hd v hh
    have h := ((classification (a::b::xs) (by simp) hp).2).1
      (by simpa only [List.length_cons,Nat.add_sub_cancel] using he)
    exact ⟨hband,h.2.2⟩
  · rintro ⟨hband,hp⟩
    have hpos : positive (a::b::xs) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hh
      · omega
      · exact positive_of_dominant hd v hh
    refine ⟨hband,?_⟩
    simpa only [List.length_cons,Nat.add_sub_cancel] using
      ((classification (a::b::xs) (by simp) hpos).2).2 ⟨hband.1,hd,hp⟩

end TaskN.Parking.Proof
