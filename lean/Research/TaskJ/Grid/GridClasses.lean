import Research.TaskJ.Grid.GridSigns

namespace Grid

open Challenge

/-- All Boolean words of a fixed length. -/
def words : ℕ → Finset (List Bool)
  | 0 => {[]}
  | k+1 => ((words k).image (false :: ·)) ∪ ((words k).image (true :: ·))

theorem mem_words {k : ℕ} {s : List Bool} : s ∈ words k ↔ s.length = k := by
  induction k generalizing s with
  | zero => simp [words]
  | succ k ih =>
    cases s with
    | nil => simp [words]
    | cons a s => cases a <;> simp [words, ih]

theorem card_words (k : ℕ) : (words k).card = 2^k := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    have hh : Disjoint ((words k).image (false :: ·)) ((words k).image (true :: ·)) := by
      simp [Finset.disjoint_left]
    rw [words, Finset.card_union_of_disjoint hh, Finset.card_image_of_injective,
      Finset.card_image_of_injective, ih, pow_succ] <;> grind [Function.Injective]

def covered (ds : List ℕ) : List Point → Finset (List Bool)
  | [] => ∅
  | x :: xs => insert (signs ds x) (insert (flip (signs ds x)) (covered ds xs))

theorem covered_mem {ds : List ℕ} {x : Point} {p : List Point} (hx : x ∈ p) :
    signs ds x ∈ covered ds p ∧ flip (signs ds x) ∈ covered ds p := by
  induction p with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst y
      simp [covered]
    · have := ih h
      simp [covered, this]

theorem covered_bound {ds : List ℕ} {x : Point} {xs : List Point}
    (h : ∀ z ∈ x :: xs, z.length = ds.length) :
    ((covered ds (x :: xs)).card : ℤ) ≤ 2 + edgeLoss ds (x :: xs) := by
  induction xs generalizing x with
  | nil =>
    have hp := Finset.card_insert_le (signs ds x) ({flip (signs ds x)} : Finset (List Bool))
    simp only [Finset.card_singleton] at hp
    simp only [covered, edgeLoss, add_zero, Finset.insert_empty]
    omega
  | cons y ys ih =>
    have ht : ∀ z ∈ y :: ys, z.length = ds.length := fun z hz => h z (by simp [hz])
    have htail := ih ht
    have hx := h x (by simp)
    have hy := ht y (by simp)
    have hm := covered_mem (ds := ds) (show y ∈ y :: ys from List.mem_cons_self)
    change ((insert (signs ds x) (insert (flip (signs ds x)) (covered ds (y :: ys)))).card : ℤ)
      ≤ 2 + (defect ds x y + edgeLoss ds (y :: ys))
    by_cases hs : signs ds x = flip (signs ds y)
    · rw [hs, flip_flip, Finset.insert_eq_of_mem hm.1, Finset.insert_eq_of_mem hm.2]
      have := defect_nonneg hx hy
      omega
    · have hd := defect_of_signs hx hy hs
      have h₁ := Finset.card_insert_le (flip (signs ds x)) (covered ds (y :: ys))
      have h₂ := Finset.card_insert_le (signs ds x) (insert (flip (signs ds x)) (covered ds (y :: ys)))
      omega

theorem all_words_covered {ds : List ℕ} {p : List Point} (h : PositiveSides ds)
    (hp : Order ds p) : words (evenCount ds) ⊆ covered ds p := by
  intro s hs
  obtain ⟨x,hx,rfl⟩ := realizes_signs h (mem_words.mp hs)
  exact (covered_mem (hp.mem_iff.mpr hx)).1

theorem even_loss {ds : List ℕ} {x : Point} {xs : List Point} (h : PositiveSides ds)
    (hp : Order ds (x :: xs)) : (2:ℤ)^evenCount ds - 2 ≤ edgeLoss ds (x :: xs) := by
  have hc := Finset.card_le_card (all_words_covered h hp)
  rw [card_words] at hc
  have hb := covered_bound (fun z hz => length_of_mem_vertices (hp.mem_iff.mp hz))
  have ht : ((2:ℕ)^evenCount ds : ℤ) ≤ (covered ds (x :: xs)).card := by exact_mod_cast hc
  push_cast at ht
  omega

end Grid
