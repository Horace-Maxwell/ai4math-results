import Research.TaskN.Parking.ParkGaps

namespace TaskN.Parking
open Challenge

@[simp] theorem subset_cons (x : ℕ) (xs : List ℕ) (t : ℕ) :
    t ∈ subsetSums (x::xs) ↔ t ∈ subsetSums xs ∨ ∃ s ∈ subsetSums xs, x+s=t := by
  simp [subsetSums]

@[simp] theorem zero_mem_subsets (xs : List ℕ) : 0 ∈ subsetSums xs := by
  induction xs with
  | nil => simp [subsetSums]
  | cons x xs ih => exact (subset_cons ..).2 (Or.inl ih)

theorem sum_mem_subsets (xs : List ℕ) : xs.sum ∈ subsetSums xs := by
  induction xs with
  | nil => simp [subsetSums]
  | cons x xs ih => exact (subset_cons ..).2 (Or.inr ⟨_,ih,rfl⟩)

theorem subset_le_sum {xs : List ℕ} {t : ℕ} (ht : t ∈ subsetSums xs) : t ≤ xs.sum := by
  induction xs generalizing t with
  | nil => simpa [subsetSums] using ht
  | cons x xs ih =>
    simp only [List.sum_cons]
    rcases (subset_cons ..).1 ht with h | ⟨s,hs,rfl⟩
    · exact (ih h).trans (by omega)
    · exact Nat.add_le_add_left (ih hs) x

theorem complement_subset {xs : List ℕ} {t : ℕ} (ht : t ∈ subsetSums xs) :
    xs.sum-t ∈ subsetSums xs := by
  induction xs generalizing t with
  | nil => simp [subsetSums]
  | cons x xs ih =>
    rw [List.sum_cons,subset_cons]
    rcases (subset_cons ..).1 ht with h | ⟨s,hs,rfl⟩
    · exact Or.inr ⟨_,ih h,by have := subset_le_sum h; omega⟩
    · exact Or.inl (by rw [show x + xs.sum - (x+s) = xs.sum-s by omega]; exact ih hs)

theorem subset_card_le (xs : List ℕ) : (subsetSums xs).card ≤ 2^xs.length := by
  induction xs with
  | nil => simp [subsetSums]
  | cons x xs ih =>
    simp only [subsetSums, List.length_cons, pow_succ]
    exact (Finset.card_union_le ..).trans (by
      have := Finset.card_image_le (s := subsetSums xs) (f := fun s : ℕ => x+s)
      omega)

theorem residual_mem {xs : List ℕ} {t : ℕ} (h : residual xs t = 0) :
    t ∈ subsetSums xs := by
  induction xs generalizing t with
  | nil => simpa [residual,subsetSums] using h
  | cons x xs ih =>
    rw [subset_cons]
    by_cases hx : x ≤ t
    · exact Or.inr ⟨_,ih (by simpa [residual,hx] using h),by omega⟩
    · exact Or.inl (ih (by simpa [residual,hx] using h))

theorem residual_of_dominant {xs : List ℕ} (hd : dominant xs) {t : ℕ}
    (ht : t ∈ subsetSums xs) : residual xs t = 0 := by
  induction xs generalizing t with
  | nil => simpa [residual,subsetSums] using ht
  | cons x xs ih =>
    change xs.sum < x ∧ dominant xs at hd
    rcases (subset_cons ..).1 ht with h | ⟨s,hs,rfl⟩
    · have hx : ¬ x ≤ t := by have := subset_le_sum h; omega
      simpa [residual,hx] using ih hd.2 h
    · simpa [residual] using ih hd.2 hs

theorem subset_card_of_dominant {xs : List ℕ} (hd : dominant xs) :
    (subsetSums xs).card = 2^xs.length := by
  induction xs with
  | nil => simp [subsetSums]
  | cons x xs ih =>
    change xs.sum < x ∧ dominant xs at hd
    have disj : Disjoint (subsetSums xs) ((subsetSums xs).image (fun s => x+s)) := by
      apply Finset.disjoint_left.mpr
      intro t ht h'
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp h'
      have := subset_le_sum ht
      omega
    rw [subsetSums,Finset.card_union_of_disjoint disj,
      Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h), ih hd.2]
    simp [pow_succ,Nat.mul_two]

theorem dominant_of_greedy_full (xs : List ℕ)
    (hcard : (subsetSums xs).card = 2^xs.length)
    (hfill : ∀ t ∈ subsetSums xs, residual xs t = 0) : dominant xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    let S := subsetSums xs
    let V := S.image (fun s => x+s)
    have hV : V.card=S.card := Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)
    have hS : S.card ≤ 2^xs.length := subset_card_le _
    change (S ∪ V).card = 2^((x::xs).length) at hcard
    simp only [List.length_cons,pow_succ] at hcard
    have hu := Finset.card_union_le S V
    have hsEq : S.card = 2^xs.length := by omega
    have disj : Disjoint S V :=
      Finset.card_union_eq_card_add_card.mp (by omega)
    have hx : xs.sum < x := by
      by_contra! hn
      have hSum : xs.sum ∈ S := sum_mem_subsets _
      have hf := hfill xs.sum ((subset_cons ..).2 (Or.inl hSum))
      have hg : residual xs (xs.sum-x) = 0 := by simpa [residual,hn] using hf
      have hm : xs.sum ∈ V :=
        Finset.mem_image.mpr ⟨_,residual_mem hg,by omega⟩
      exact Finset.disjoint_left.mp disj hSum hm
    refine ⟨hx,ih hsEq ?_⟩
    intro s hs
    have hnx : ¬ x ≤ s := by have := subset_le_sum hs; omega
    simpa [residual,hnx] using hfill s ((subset_cons ..).2 (Or.inl hs))

end TaskN.Parking
