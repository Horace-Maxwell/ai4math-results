import Research.Backfill.Paper8.Challenge

/-!
# Paper 8, standard leaf sums (`StdLeafSums`)

The standard leaf sums `λ°_i = lamStd a i` satisfy `|λ°_i| ≤ a_i` and `λ°_i ≡ a_i (mod 2)`,
(P1) and (P2). Proof by cases on `a i` and on the position `posIn a i` of `i` in `I_{a_i}`; for
(P1) the two smallest elements of `I_b` (obtained with `Finset.min'`) have positions `0` and `1`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge

namespace P8Real

section Std

variable {k : ℕ} (a : Fin k → ℕ)

/-- `k_b = |I_b|`. -/
theorem kb_eq_card_Ib (b : ℕ) : kb (branchMS a) b = (Ib a b).card := by
  simp only [kb, branchMS, Ib, Multiset.count_map, Finset.card, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro x _
  exact eq_comm

theorem mem_Ib {b : ℕ} {i : Fin k} : i ∈ Ib a b ↔ a i = b := by
  simp [Ib]

/-- The smallest element of `I_b` has position `0`. -/
theorem posIn_min' (b : ℕ) (h : (Ib a b).Nonempty) : posIn a ((Ib a b).min' h) = 0 := by
  have hmem : (Ib a b).min' h ∈ Ib a b := Finset.min'_mem _ _
  have hb : a ((Ib a b).min' h) = b := (mem_Ib a).1 hmem
  unfold posIn
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro j - ⟨hj, hja⟩
  have hj' : j ∈ Ib a b := (mem_Ib a).2 (hja.trans hb)
  exact absurd (Finset.min'_le _ _ hj') (not_le.2 hj)

/-- The second smallest element of `I_b` has position `1`. -/
theorem posIn_second (b : ℕ) (h : (Ib a b).Nonempty)
    (h2 : ((Ib a b).erase ((Ib a b).min' h)).Nonempty) :
    posIn a (((Ib a b).erase ((Ib a b).min' h)).min' h2) = 1 := by
  set i0 := (Ib a b).min' h
  set i1 := ((Ib a b).erase i0).min' h2
  have hi1 : i1 ∈ (Ib a b).erase i0 := Finset.min'_mem _ _
  have hi1' := Finset.mem_erase.1 hi1
  have hi0 : i0 ∈ Ib a b := Finset.min'_mem _ _
  have hb1 : a i1 = b := (mem_Ib a).1 hi1'.2
  have hb0 : a i0 = b := (mem_Ib a).1 hi0
  have hlt : i0 < i1 := lt_of_le_of_ne (Finset.min'_le _ _ hi1'.2) (Ne.symm hi1'.1)
  unfold posIn
  rw [Finset.card_eq_one]
  refine ⟨i0, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hja⟩
    by_contra hne
    have hj' : j ∈ (Ib a b).erase i0 :=
      Finset.mem_erase.2 ⟨hne, (mem_Ib a).2 (hja.trans hb1)⟩
    exact absurd (Finset.min'_le _ _ hj') (not_le.2 hj)
  · rintro rfl
    exact ⟨hlt, hb0.trans hb1.symm⟩

/-- `|λ°_i| ≤ a_i` and `λ°_i ≡ a_i (mod 2)` for `a_i ≥ 1`. -/
theorem lamStd_bound (i : Fin k) (hi : 1 ≤ a i) :
    |lamStd a i| ≤ (a i : ℤ) ∧ Even (lamStd a i - (a i : ℤ)) := by
  rw [abs_le, Int.even_iff]
  unfold lamStd
  split_ifs <;> omega

/-- (P2): for `a_i ≥ 2` and `i` smallest in `I_{a_i}`, `|λ°_i| < a_i`. -/
theorem lamStd_small (i : Fin k) (hi : 2 ≤ a i) (hpos : posIn a i = 0) :
    |lamStd a i| < (a i : ℤ) := by
  rw [abs_lt]
  unfold lamStd
  rw [hpos]
  split_ifs <;> omega

/-- (P1): for `b ≥ 1` with `k_b ≥ 2` the `λ°_i`, `i ∈ I_b`, are not all equal. -/
theorem lamStd_not_const (b : ℕ) (hb : 1 ≤ b) (hkb : 2 ≤ kb (branchMS a) b) :
    ∃ i ∈ Ib a b, ∃ i' ∈ Ib a b, lamStd a i ≠ lamStd a i' := by
  rw [kb_eq_card_Ib] at hkb
  have h : (Ib a b).Nonempty := Finset.card_pos.1 (by omega)
  have h2 : ((Ib a b).erase ((Ib a b).min' h)).Nonempty := by
    apply Finset.card_pos.1
    rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]
    omega
  set i0 := (Ib a b).min' h
  set i1 := ((Ib a b).erase i0).min' h2
  have hi0 : i0 ∈ Ib a b := Finset.min'_mem _ _
  have hi1 : i1 ∈ Ib a b := (Finset.mem_erase.1 (Finset.min'_mem _ h2)).2
  have hb0 : a i0 = b := (mem_Ib a).1 hi0
  have hb1 : a i1 = b := (mem_Ib a).1 hi1
  have hp0 : posIn a i0 = 0 := posIn_min' a b h
  have hp1 : posIn a i1 = 1 := posIn_second a b h h2
  have hkb' : 2 ≤ kb (branchMS a) b := by rw [kb_eq_card_Ib]; exact hkb
  refine ⟨i0, hi0, i1, hi1, ?_⟩
  unfold lamStd
  rw [hb0, hb1, hp0, hp1]
  split_ifs <;> simp_all

theorem stdLeafSums : StdLeafSums := by
  intro k a
  exact ⟨fun i hi => lamStd_bound a i hi,
    fun b _ hb hkb => lamStd_not_const a b hb hkb,
    fun i hi hpos => lamStd_small a i hi hpos⟩

end Std

end P8Real
