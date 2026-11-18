import Research.TaskH.General.ColorWordsStrict

/-!
A closed proper k-color word with length k*a and at most a descents is
tight. Its actual first k entries cover all colors. Equal starting rank
therefore determines a whole good permutation, giving the one-direction
bound k without an assumed periodicity or rainbow premise.
-/

set_option autoImplicit false

namespace TaskH.General.ColorWords

open _root_.TaskH.ColorWords

variable {k : ℕ}

theorem closed_tight (hk : 3 ≤ k) (w : ℕ → Fin k) (L a : ℕ)
    (hlen : L = k * a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hclosed : w L = w 0) (hcount : descents w L ≤ a) :
    descents w L = a ∧
      L + (w 0).val = (w L).val + k * descents w L := by
  have hc := endpoint_capacity w L hne
  rw [hclosed] at hc
  have hprod : k * a ≤ k * descents w L := by omega
  have hge : a ≤ descents w L :=
    le_of_mul_le_mul_left hprod (by omega : 0 < k)
  have he : descents w L = a := Nat.le_antisymm hcount hge
  exact ⟨he, by rw [hclosed, he, hlen]; omega⟩

/-- No color-cover premise is supplied: it follows from the actual word. -/
theorem closed_prefix_surjective (hk : 3 ≤ k) (w : ℕ → Fin k) (L a : ℕ)
    (hlen : L = k * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hclosed : w L = w 0) (hcount : descents w L ≤ a) :
    Function.Surjective (fun i : Fin k => w i.val) := by
  have ht := (closed_tight hk w L a hlen hne hclosed hcount).2
  have hkL : k ≤ L := by
    rw [hlen]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left k ha
  exact tight_prefix_surjective hk w L hkL hne ht

/-- The same actual word and starting rank determine an entire good order. -/
theorem closed_orders_eq_of_start (hk : 3 ≤ k) (w : ℕ → Fin k) (L a : ℕ)
    (hlen : L = k * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) (hclosed : w L = w 0)
    (π ρ : Equiv.Perm (Fin k))
    (hπ : descents (fun i => π (w i)) L ≤ a)
    (hρ : descents (fun i => ρ (w i)) L ≤ a)
    (hstart : π (w 0) = ρ (w 0)) : π = ρ := by
  have hpne : ∀ i : ℕ, i < L → π (w i) ≠ π (w (i + 1)) :=
    fun i hi => π.injective.ne (hne i hi)
  have hrne : ∀ i : ℕ, i < L → ρ (w i) ≠ ρ (w (i + 1)) :=
    fun i hi => ρ.injective.ne (hne i hi)
  have hpclosed : π (w L) = π (w 0) := congrArg π hclosed
  have hrclosed : ρ (w L) = ρ (w 0) := congrArg ρ hclosed
  have hpt := (closed_tight hk (fun i => π (w i)) L a hlen hpne hpclosed hπ).2
  have hrt := (closed_tight hk (fun i => ρ (w i)) L a hlen hrne hrclosed hρ).2
  have hkL : k ≤ L := by
    rw [hlen]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left k ha
  have hpref : ∀ i : Fin k, π (w i.val) = ρ (w i.val) := by
    intro i
    have hiL : i.val ≤ L := by have := i.isLt; omega
    have hpi := tight_word_get (fun j => π (w j)) L hpne hpt i.val hiL
    have hri := tight_word_get (fun j => ρ (w j)) L hrne hrt i.val hiL
    rw [hpi, hri, hstart]
  have hpsurj := closed_prefix_surjective hk (fun i => π (w i)) L a
    hlen ha hpne hpclosed hπ
  apply Equiv.ext
  intro c
  obtain ⟨i, hi⟩ := hpsurj (π c)
  have hw : w i.val = c := π.injective hi
  rw [← hw]
  exact hpref i

/-- Actual one-direction good orders inject into their initial Fin k rank. -/
theorem closed_low_descent_orders_card_le (hk : 3 ≤ k) (w : ℕ → Fin k) (L a : ℕ)
    (hlen : L = k * a) (ha : 1 ≤ a)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) (hclosed : w L = w 0) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
      descents (fun i => π (w i)) L ≤ a)).card ≤ k := by
  classical
  calc
    (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        descents (fun i => π (w i)) L ≤ a)).card ≤
        (Finset.univ : Finset (Fin k)).card := by
      apply Finset.card_le_card_of_injOn (fun π : Equiv.Perm (Fin k) => π (w 0))
      · intro π _
        exact Finset.mem_univ _
      · intro π hπ ρ hρ he
        exact closed_orders_eq_of_start hk w L a hlen ha hne hclosed π ρ
          (Finset.mem_filter.mp hπ).2 (Finset.mem_filter.mp hρ).2 he
    _ = k := by simp

end TaskH.General.ColorWords

#print axioms TaskH.General.ColorWords.closed_tight
#print axioms TaskH.General.ColorWords.closed_prefix_surjective
#print axioms TaskH.General.ColorWords.closed_orders_eq_of_start
#print axioms TaskH.General.ColorWords.closed_low_descent_orders_card_le
