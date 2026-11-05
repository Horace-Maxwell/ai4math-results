import Research.Backfill.Paper7.GapPartition

/-! First positive returns to a supported vertex, with exact connections to
the frozen inGap and evenGaps predicates. This is an uncompiled source candidate. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators
open Fin.NatCast

namespace Paper7Lemma22Gaps
open BackfillPaper7.Challenge

theorem exists_pos_hit (b : ℕ) (K : Finset (Fin b)) (k : Fin b) (hk : k ∈ K) :
    ∃ n : ℕ, 0 < n ∧ ((finRotate b) ^ n) k ∈ K := by
  refine ⟨b, lt_of_le_of_lt (Nat.zero_le k.val) k.isLt, ?_⟩
  rw [rotate_pow_card_apply]
  exact hk
#print axioms Paper7Lemma22Gaps.exists_pos_hit

def firstHitLength (b : ℕ) (K : Finset (Fin b)) (k : Fin b) (hk : k ∈ K) : ℕ :=
  Nat.find (exists_pos_hit b K k hk)
#print axioms Paper7Lemma22Gaps.firstHitLength

theorem firstHitLength_pos (b : ℕ) (K : Finset (Fin b)) (k : Fin b) (hk : k ∈ K) :
    0 < firstHitLength b K k hk :=
  (Nat.find_spec (exists_pos_hit b K k hk)).1
#print axioms Paper7Lemma22Gaps.firstHitLength_pos

theorem firstHitLength_le_card (b : ℕ) (K : Finset (Fin b)) (k : Fin b)
    (hk : k ∈ K) : firstHitLength b K k hk ≤ b := by
  apply Nat.find_min' (exists_pos_hit b K k hk)
  refine ⟨lt_of_le_of_lt (Nat.zero_le k.val) k.isLt, ?_⟩
  rw [rotate_pow_card_apply]
  exact hk
#print axioms Paper7Lemma22Gaps.firstHitLength_le_card

theorem firstHitLength_mem (b : ℕ) (K : Finset (Fin b)) (k : Fin b) (hk : k ∈ K) :
    ((finRotate b) ^ firstHitLength b K k hk) k ∈ K :=
  (Nat.find_spec (exists_pos_hit b K k hk)).2
#print axioms Paper7Lemma22Gaps.firstHitLength_mem

theorem firstHitLength_clear (b : ℕ) (K : Finset (Fin b)) (k : Fin b) (hk : k ∈ K)
    (t : ℕ) (htpos : 0 < t) (htd : t < firstHitLength b K k hk) :
    ((finRotate b) ^ t) k ∉ K := by
  intro htmem
  exact Nat.find_min (exists_pos_hit b K k hk) htd ⟨htpos, htmem⟩
#print axioms Paper7Lemma22Gaps.firstHitLength_clear

theorem firstHitLength_eq_of_first_hit (b : ℕ) (K : Finset (Fin b))
    (k : Fin b) (hk : k ∈ K) (d : ℕ) (hdpos : 0 < d)
    (hmem : ((finRotate b) ^ d) k ∈ K)
    (hclear : ∀ t : ℕ, 0 < t → t < d → ((finRotate b) ^ t) k ∉ K) :
    firstHitLength b K k hk = d := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (exists_pos_hit b K k hk) ⟨hdpos, hmem⟩
  · by_contra hnot
    have hlt : firstHitLength b K k hk < d := by omega
    exact hclear _ (firstHitLength_pos b K k hk) hlt (firstHitLength_mem b K k hk)
#print axioms Paper7Lemma22Gaps.firstHitLength_eq_of_first_hit

/-- Rotation indices below one full turn are unique. -/
theorem rotate_pow_index_injective (b : ℕ) (k : Fin b) (t u : ℕ)
    (ht : t < b) (hu : u < b)
    (he : ((finRotate b) ^ t) k = ((finRotate b) ^ u) k) : t = u := by
  let : NeZero b := k.neZero
  rw [rotate_pow_apply, rotate_pow_apply] at he
  have hcast : (t : Fin b) = (u : Fin b) := add_left_cancel he
  have hval := congrArg Fin.val hcast
  simpa only [Fin.val_cast_of_lt ht, Fin.val_cast_of_lt hu] using hval
#print axioms Paper7Lemma22Gaps.rotate_pow_index_injective

theorem inGap_iff_before_firstHit (b : ℕ) (K : Finset (Fin b))
    (k : Fin b) (hk : k ∈ K) (j : Fin b) :
    inGap b K k j ↔ ∃ t : ℕ, 0 < t ∧ t < firstHitLength b K k hk ∧
      ((finRotate b) ^ t) k = j := by
  constructor
  · rintro ⟨t, ht, hend, hclear⟩
    have htbounds := Finset.mem_Icc.mp ht
    have htd : t < firstHitLength b K k hk := by
      by_contra hnot
      have hdle : firstHitLength b K k hk ≤ t := by omega
      have hbad := hclear (firstHitLength b K k hk)
        (Finset.mem_Icc.mpr ⟨firstHitLength_pos b K k hk, hdle⟩)
      exact hbad (firstHitLength_mem b K k hk)
    exact ⟨t, htbounds.1, htd, hend⟩
  · rintro ⟨t, htpos, htd, hend⟩
    have hdb := firstHitLength_le_card b K k hk
    refine ⟨t, Finset.mem_Icc.mpr ⟨htpos, by omega⟩, hend, ?_⟩
    intro s hs
    have hsbounds := Finset.mem_Icc.mp hs
    exact firstHitLength_clear b K k hk s hsbounds.1 (by omega)
#print axioms Paper7Lemma22Gaps.inGap_iff_before_firstHit

/-- The endpoint witness in frozen evenGaps must be the first positive hit. -/
theorem evenGap_iff_even_firstHitLength (b : ℕ) (K : Finset (Fin b))
    (k : Fin b) (hk : k ∈ K) :
    (∃ d ∈ Finset.Icc 1 b, Even d ∧ ((finRotate b) ^ d) k ∈ K ∧
      ∀ t ∈ Finset.Ico 1 d, ((finRotate b) ^ t) k ∉ K) ↔
      Even (firstHitLength b K k hk) := by
  constructor
  · rintro ⟨d, hd, heven, hmem, hclear⟩
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have he : firstHitLength b K k hk = d :=
      firstHitLength_eq_of_first_hit b K k hk d hdpos hmem (by
        intro t htpos htd
        exact hclear t (Finset.mem_Ico.mpr ⟨htpos, htd⟩))
    simpa only [he] using heven
  · intro heven
    refine ⟨firstHitLength b K k hk,
      Finset.mem_Icc.mpr ⟨firstHitLength_pos b K k hk, firstHitLength_le_card b K k hk⟩,
      heven, firstHitLength_mem b K k hk, ?_⟩
    intro t ht
    have htbounds := Finset.mem_Ico.mp ht
    exact firstHitLength_clear b K k hk t htbounds.1 htbounds.2
#print axioms Paper7Lemma22Gaps.evenGap_iff_even_firstHitLength

/-- Exact original even-gap count, including the singleton-support wrap gap. -/
theorem evenGaps_eq_sum_firstHit (b : ℕ) (K : Finset (Fin b)) :
    evenGaps b K = ∑ k : {k : Fin b // k ∈ K},
      if Even (firstHitLength b K k.1 k.2) then 1 else 0 := by
  classical
  let P : Fin b → Prop := fun k => ∃ d ∈ Finset.Icc 1 b,
    Even d ∧ ((finRotate b) ^ d) k ∈ K ∧
      ∀ t ∈ Finset.Ico 1 d, ((finRotate b) ^ t) k ∉ K
  change (K.filter P).card = _
  rw [Finset.card_filter]
  rw [← Finset.sum_coe_sort K (fun k => if P k then (1 : ℕ) else 0)]
  apply Finset.sum_congr rfl
  intro k _
  have hp : P k.1 ↔ Even (firstHitLength b K k.1 k.2) :=
    evenGap_iff_even_firstHitLength b K k.1 k.2
  simp only [hp]
#print axioms Paper7Lemma22Gaps.evenGaps_eq_sum_firstHit

end Paper7Lemma22Gaps
