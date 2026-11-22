import Research.TaskN.Parking.ParkWalk

namespace TaskN.Parking
open Challenge

theorem point_iff_take (s : List ℕ) (v : ℕ) :
    v ∈ points s ↔ ∃ i ≤ s.length, (s.take i).sum = v := by
  induction s generalizing v with
  | nil => simp [points,eq_comm]
  | cons x s ih =>
    rw [point_cons]
    constructor
    · rintro (rfl | ⟨u,hu,rfl⟩)
      · exact ⟨0,Nat.zero_le _,by simp⟩
      · obtain ⟨i,hi,rfl⟩ := (ih u).1 hu
        exact ⟨i+1,Nat.succ_le_succ hi,by simp⟩
    · rintro ⟨i,hi,rfl⟩
      cases i with
      | zero => simp
      | succ i =>
        exact Or.inr ⟨_,(ih _).2 ⟨i,Nat.le_of_succ_le_succ hi,rfl⟩,by simp⟩

theorem take_sum_inj {s : List ℕ} (hs : positive s) (i j : ℕ) (hi : i≤ s.length)
    (hj : j≤ s.length) (he : (s.take i).sum=(s.take j).sum) : i=j := by
  induction s generalizing i j with
  | nil => simp_all
  | cons x s ih =>
    have hx : 0<x := hs _ (by simp)
    cases i <;> cases j
    · rfl
    · simp at he; omega
    · simp at he; omega
    · rename_i i j
      apply congrArg Nat.succ
      exact ih (positive_tail hs) i j (Nat.le_of_succ_le_succ hi)
        (Nat.le_of_succ_le_succ hj) (by simpa using he)

private theorem cut (s : List ℕ) (i v : ℕ) (hv : v ≤ (s.take i).sum) :
    v ∈ points s ↔ v ∈ points (s.take i) := by
  have hcat := point_append (s.take i) (s.drop i) v
  rw [List.take_append_drop] at hcat
  refine hcat.trans ⟨?_,Or.inl⟩
  rintro (h | ⟨w,_,hw⟩)
  · exact h
  · have hEq : v=(s.take i).sum := by omega
    exact hEq ▸ end_point _

theorem prefixSymmetric_take {xs : List ℕ} (hd : dominant xs) (i : ℕ) :
    prefixSymmetric xs (((ruler (jumps xs)).take i).sum) ↔ pal ((ruler (jumps xs)).take i) := by
  let w := ruler (jumps xs)
  let pre := w.take i
  obtain ⟨_,hp,he⟩ := walk_of_dominant xs hd
  have hall : positive pre := fun x hx => hp x (List.mem_of_mem_take hx)
  have hEnd : pre.sum ∈ subsetSums xs := by
    rw [←he]; exact (cut w i _ (Nat.le_refl _)).2 (end_point pre)
  change (pre.sum ∈ subsetSums xs ∧ ∀ s ∈ subsetSums xs, s ≤ pre.sum →
    pre.sum-s ∈ subsetSums xs) ↔ pal pre
  rw [←symmetric_iff_pal hall]
  constructor
  · rintro ⟨_,hsym⟩ s hs
    have hl := point_bound hs
    have hs' : s ∈ subsetSums xs := by rw [←he]; exact (cut w i s hl).2 hs
    have hv := hsym s hs' hl
    rw [←he] at hv
    exact (cut w i _ (Nat.sub_le _ _)).1 hv
  · intro h
    refine ⟨hEnd,?_⟩
    intro s hs hl
    rw [←he] at hs ⊢
    exact (cut w i _ (Nat.sub_le _ _)).2 (h s ((cut w i s hl).1 hs))

end TaskN.Parking
