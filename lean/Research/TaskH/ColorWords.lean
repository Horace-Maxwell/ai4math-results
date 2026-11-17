import Mathlib

/-!
Finite color-word lemmas for Task H.

Only the first `L + 1` entries of a word `ℕ → Fin k` are used. The
recursive descent count counts the actual adjacent strict descents among its
first `L` edges. The capacity inequality proves the increasing-prefix fact
needed in the over-deleted-vertex part of the color-order multiplicity bound.

No graph-level hypotheses, rainbow assumptions, or equality-case conclusions
are introduced as substitute assumptions here.
-/

set_option autoImplicit false

namespace TaskH.ColorWords

variable {k : ℕ}

/-- Number of strict descents among the first `L` edges of a color word. -/
def descents (w : ℕ → Fin k) : ℕ → ℕ
  | 0 => 0
  | L + 1 => descents w L + if w (L + 1) < w L then 1 else 0

@[simp] theorem descents_zero (w : ℕ → Fin k) : descents w 0 = 0 := rfl

theorem descents_succ (w : ℕ → Fin k) (L : ℕ) :
    descents w (L + 1) = descents w L + if w (L + 1) < w L then 1 else 0 := rfl

/-- Splitting the path at a vertex splits its descent count exactly. -/
theorem descents_add (w : ℕ → Fin k) (m n : ℕ) :
    descents w (m + n) =
      descents w m + descents (fun i => w (m + i)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.add_succ, descents_succ, ih, Nat.add_assoc, Nat.add_zero]

/-- Each ascent contributes at least one to the color value, and a descent
can lose at most `k - 1`. This is the endpoint form of the run-capacity bound. -/
theorem endpoint_capacity (w : ℕ → Fin k) (L : ℕ)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) :
    L + (w 0).val ≤ (w L).val + k * descents w L := by
  revert hne
  induction L with
  | zero =>
    intro _hne
    simp
  | succ L ih =>
    intro hne
    have hi := ih (fun i hi => hne i (by omega))
    have hbound := (w L).isLt
    by_cases hd : w (L + 1) < w L
    · simp only [descents_succ, ite_eq_left hd, Nat.mul_add, Nat.mul_one]
      omega
    · have hneq : (w L).val ≠ (w (L + 1)).val := by
        intro he
        exact hne L (by omega) (Fin.ext he)
      have hnot : ¬ (w (L + 1)).val < (w L).val := hd
      have hstep : (w L).val + 1 ≤ (w (L + 1)).val := by omega
      simp only [descents_succ, ite_eq_right hd, Nat.add_zero]
      omega

/-- A proper word with `D` descents has at most `k * (D + 1)` vertices. -/
theorem word_capacity (w : ℕ → Fin k) (L : ℕ)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) :
    L + 1 ≤ k * (descents w L + 1) := by
  have h := endpoint_capacity w L hne
  have hbound := (w L).isLt
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Every block of `k` edges of a proper color word has a descent. -/
theorem positive_descents_of_k_edges (w : ℕ → Fin k)
    (hne : ∀ i : ℕ, i < k → w i ≠ w (i + 1)) :
    0 < descents w k := by
  have hc := word_capacity w k hne
  by_contra hn
  have hz : descents w k = 0 := by omega
  simp only [hz, zero_add, Nat.mul_one] at hc
  omega

/-- For `k * (b + 1) - 1` vertices and at most `b` descents, all of the first
`k - 2` edges ascend. The statement uses an equality without natural subtraction
to record the exact word length. -/
theorem prefix_ascent (w : ℕ → Fin k) (L b : ℕ)
    (hlen : L + 2 = k * (b + 1))
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hcount : descents w L ≤ b) (j : ℕ) (hj : j + 2 < k) :
    w j < w (j + 1) := by
  have hlen' : L + 2 = k * b + k := by
    simpa only [Nat.mul_add, Nat.mul_one] using hlen
  have hjL : j < L := by omega
  by_contra hnot
  have hneq : (w j).val ≠ (w (j + 1)).val := by
    intro he
    exact hne j hjL (Fin.ext he)
  have hnot' : ¬ (w j).val < (w (j + 1)).val := hnot
  have hd : w (j + 1) < w j := by
    change (w (j + 1)).val < (w j).val
    omega
  have hadd : (j + 1) + (L - (j + 1)) = L := by omega
  have hsplit := descents_add w (j + 1) (L - (j + 1))
  rw [hadd, descents_succ, ite_eq_left hd] at hsplit
  have htail : descents (fun i => w (j + 1 + i)) (L - (j + 1)) + 1 ≤ b := by
    omega
  have hcapacity := word_capacity (fun i => w (j + 1 + i)) (L - (j + 1))
    (fun i hi => hne (j + 1 + i) (by omega))
  have hmul := Nat.mul_le_mul_left k htail
  omega

/-- Consequently the first `k - 1` colors are strictly increasing. -/
theorem prefix_strictMono (hk : 3 ≤ k) (w : ℕ → Fin k) (L b : ℕ)
    (hlen : L + 2 = k * (b + 1))
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hcount : descents w L ≤ b) :
    StrictMono (fun i : Fin (k - 1) => w i.val) := by
  have hmono : StrictMonoOn w (Set.Iic (k - 2)) :=
    strictMonoOn_Iic_of_lt_succ (fun i hi =>
      prefix_ascent w L b hlen hne hcount i (by omega))
  intro i j hij
  change w i.val < w j.val
  exact hmono (by have := i.isLt; change i.val ≤ k - 2; omega)
    (by have := j.isLt; change j.val ≤ k - 2; omega) hij

theorem prefix_injective (hk : 3 ≤ k) (w : ℕ → Fin k) (L b : ℕ)
    (hlen : L + 2 = k * (b + 1))
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hcount : descents w L ≤ b) :
    Function.Injective (fun i : Fin (k - 1) => w i.val) :=
  (prefix_strictMono hk w L b hlen hne hcount).injective

/-- A color permutation preserves adjacent inequality, so the monotone-prefix
lemma applies directly to a rank order on the original color word. -/
theorem ranked_prefix_strictMono (hk : 3 ≤ k) (w : ℕ → Fin k)
    (π : Equiv.Perm (Fin k)) (L b : ℕ)
    (hlen : L + 2 = k * (b + 1))
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hcount : descents (fun i => π (w i)) L ≤ b) :
    StrictMono (fun i : Fin (k - 1) => π (w i.val)) := by
  exact prefix_strictMono hk (fun i => π (w i)) L b hlen
    (fun i hi => π.injective.ne (hne i hi)) hcount

theorem ranked_prefix_injective (hk : 3 ≤ k) (w : ℕ → Fin k)
    (π : Equiv.Perm (Fin k)) (L b : ℕ)
    (hlen : L + 2 = k * (b + 1))
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hcount : descents (fun i => π (w i)) L ≤ b) :
    Function.Injective (fun i : Fin (k - 1) => w i.val) := by
  intro i j hij
  apply (ranked_prefix_strictMono hk w π L b hlen hne hcount).injective
  exact congrArg π hij

end TaskH.ColorWords

#print axioms TaskH.ColorWords.descents_add
#print axioms TaskH.ColorWords.endpoint_capacity
#print axioms TaskH.ColorWords.word_capacity
#print axioms TaskH.ColorWords.positive_descents_of_k_edges
#print axioms TaskH.ColorWords.prefix_ascent
#print axioms TaskH.ColorWords.prefix_strictMono
#print axioms TaskH.ColorWords.ranked_prefix_injective
