import Research.TaskN.Parking.ParkSums

namespace TaskN.Parking
open Challenge
open scoped Classical

private noncomputable def offsets (ys : List ℕ) : Finset ℕ :=
  (Finset.range ys.sum).filter (allPositions ys)

private theorem card_offsets (ys : List ℕ) : (W ys).card = (offsets ys).card :=
  Finset.card_image_of_injective _ Nat.succ_injective

private theorem firstCar {a t : ℕ} {xs : List ℕ} (h : allPositions (a::xs) t) :
    residual xs t = 0 := by
  simpa using (allPositions_iff _ _).1 h [] a xs rfl

private theorem offsets_subset (a : ℕ) (xs : List ℕ) : offsets (a::xs) ⊆ subsetSums xs := by
  intro t ht
  exact residual_mem (firstCar (Finset.mem_filter.mp ht).2)

theorem W_bound (a : ℕ) (xs : List ℕ) : (W (a::xs)).card ≤ 2^xs.length := by
  rw [card_offsets]
  exact (Finset.card_le_card (offsets_subset ..)).trans (subset_card_le _)

private theorem card_eq_iff (a : ℕ) (xs : List ℕ) (ha : 0<a) :
    (W (a::xs)).card = 2^xs.length ↔
    (subsetSums xs).card = 2^xs.length ∧ ∀ t ∈ subsetSums xs, allPositions (a::xs) t := by
  rw [card_offsets]
  have hi := offsets_subset a xs
  constructor
  · intro he
    have c₁ := Finset.card_le_card hi
    have c₂ := subset_card_le xs
    have eqs := Finset.eq_of_subset_of_card_le hi (by omega)
    refine ⟨by omega, fun t ht => ?_⟩
    rw [←eqs] at ht
    exact (Finset.mem_filter.mp ht).2
  · rintro ⟨hc, hall⟩
    have rev : subsetSums xs ⊆ offsets (a::xs) := by
      intro t ht
      have hlim := subset_le_sum ht
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by simp only [List.sum_cons]; omega), hall t ht⟩
    rwa [Finset.Subset.antisymm hi rev]

private def shiftClosed (xs : List ℕ) (d : ℕ) : Prop :=
  ∀ s ∈ subsetSums xs, d ≤ s → s-d ∈ subsetSums xs

private theorem shift_iff_prefix (xs : List ℕ) (d : ℕ) :
    shiftClosed xs d ↔ xs.sum ≤ d ∨ prefixSymmetric xs (xs.sum-d) := by
  constructor
  · intro hh
    by_cases hd : xs.sum ≤ d
    · exact Or.inl hd
    · refine Or.inr ⟨hh _ (sum_mem_subsets xs) (by omega),?_⟩
      intro s hs hsz
      have hd' : d ≤ xs.sum-s := by omega
      have hh' := hh _ (complement_subset hs) hd'
      rwa [show xs.sum-s-d = xs.sum-d-s by omega] at hh'
  · intro hp s hs hds
    have hlim := subset_le_sum hs
    rcases hp with hd | ⟨_,hsym⟩
    · rw [show s-d=0 by omega]
      exact zero_mem_subsets _
    · have hsz : xs.sum-s ≤ xs.sum-d := by omega
      have hx := hsym _ (complement_subset hs) hsz
      rwa [show xs.sum-d-(xs.sum-s) = s-d by omega] at hx

private theorem full_iff_shift (a b : ℕ) (xs : List ℕ) (hab : b≤a)
    (hd : dominant (b::xs)) :
    (∀ t ∈ subsetSums (b::xs), allPositions (a::b::xs) t) ↔ shiftClosed xs (a-b) := by
  have hdom : xs.sum < b ∧ dominant xs := hd
  constructor
  · intro hall s hs _
    have hmem := (subset_cons b xs (b+s)).2 (Or.inr ⟨s,hs,rfl⟩)
    have h₂ := (allPositions_iff _ _).1 (hall _ hmem) [a] b xs rfl
    have hsub : b+s-[a].sum = s-(a-b) := by simp; omega
    rw [hsub] at h₂
    exact residual_mem h₂
  · intro hh t ht
    apply (allPositions_iff _ _).2
    intro pre x suf he
    cases pre with
    | nil =>
      cases he
      simpa using residual_of_dominant hd ht
    | cons head pre =>
      cases pre with
      | nil =>
        cases he
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
        rcases (subset_cons ..).1 ht with h | ⟨s,hs,rfl⟩
        · have ht0 : t-a=0 := by have := subset_le_sum h; omega
          rw [ht0,residual_zero]
        · by_cases hds : a-b ≤ s
          · have hsub : b+s-a=s-(a-b) := by omega
            rw [hsub]
            exact residual_of_dominant hdom.2 (hh _ hs hds)
          · rw [show b+s-a=0 by omega,residual_zero]
      | cons second more =>
        cases he
        have hlim := subset_le_sum ht
        simp only [List.sum_cons] at hlim ⊢
        have hz : t-(a+(b+more.sum))=0 := by omega
        rw [hz,residual_zero]

theorem classification : ExtremalClassification := by
  intro lengths hn hp
  cases lengths with
  | nil => exact (hn rfl).elim
  | cons a xs =>
    have ha : 0 < a := hp a (by simp)
    simp only [List.length_cons,Nat.add_sub_cancel] 
    refine ⟨W_bound a xs,?_⟩
    cases xs with
    | nil =>
      change (W [a]).card = 2^(([] : List ℕ).length) ↔ True
      apply iff_true_intro
      apply (card_eq_iff a [] ha).2
      refine ⟨by simp [subsetSums],?_⟩
      intro t ht
      have hz : t=0 := by simpa [subsetSums] using ht
      subst t
      apply (allPositions_iff _ _).2
      intro pre x suf _
      simp
    | cons b xs =>
      rw [card_eq_iff a (b::xs) ha]
      constructor
      · rintro ⟨hcard,hall⟩
        have hd := dominant_of_greedy_full (b::xs) hcard (fun t ht => firstCar (hall t ht))
        have hh := (allPositions_iff _ _).1 (hall _ (sum_mem_subsets (b::xs))) [a] b xs rfl
        have hlim := subset_le_sum (residual_mem hh)
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at hlim
        have hab : b ≤ a := by omega
        exact ⟨hab,hd,(shift_iff_prefix ..).1 ((full_iff_shift a b xs hab hd).1 hall)⟩
      · rintro ⟨hab,hd,hpre⟩
        exact ⟨subset_card_of_dominant hd,
          (full_iff_shift a b xs hab hd).2 ((shift_iff_prefix ..).2 hpre)⟩

end TaskN.Parking
