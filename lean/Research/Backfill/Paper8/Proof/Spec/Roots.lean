import Research.Backfill.Paper8.Proof.Spec.Secular

/-!
# Paper 8, Lemma 3.1(i), numerical part: the roots of `R`

With `b_1 < ⋯ < b_r` the increasing enumeration of `B` (`Finset.orderEmbOfFin`), the signs of
`R(b_j)` alternate and `R(b* + |m| + 1) > 0`; the intermediate value theorem gives a root in each
interval `(b_j, b_{j+1})` and in `(b_r, ∞)`. These `r` roots are distinct and `deg R = r`, so they
are all the roots (`roots_spec`).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Polynomial

namespace P8Spec

section

variable (m : Multiset ℕ)

/-- Every element of `B` is `b_i` for some `i`. -/
theorem exists_orderEmb_eq (c : ℕ) (hc : c ∈ Bset m) :
    ∃ i : Fin (Bset m).card, (Bset m).orderEmbOfFin rfl i = c := by
  have : c ∈ Set.range ((Bset m).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hc
  exact this

/-- The number of elements of `B` larger than `b`. -/
def nAbove (b : ℕ) : ℕ := ((Bset m).filter (fun c => b < c)).card

theorem nAbove_succ (j : Fin (Bset m).card) (h : j.val + 1 < (Bset m).card) :
    nAbove m ((Bset m).orderEmbOfFin rfl j) =
      nAbove m ((Bset m).orderEmbOfFin rfl ⟨j.val + 1, h⟩) + 1 := by
  set bs := (Bset m).orderEmbOfFin rfl with hbs
  have hfilter : (Bset m).filter (fun c => bs j < c) =
      insert (bs ⟨j.val + 1, h⟩) ((Bset m).filter (fun c => bs ⟨j.val + 1, h⟩ < c)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hc, hlt⟩
      obtain ⟨i, rfl⟩ := exists_orderEmb_eq m c hc
      have hji : j < i := bs.lt_iff_lt.1 hlt
      by_cases hi : i = ⟨j.val + 1, h⟩
      · left
        rw [hi]
      · right
        refine ⟨hc, bs.lt_iff_lt.2 ?_⟩
        rw [Fin.lt_def] at hji ⊢
        rw [Fin.ext_iff] at hi
        simp only at hi ⊢
        omega
    · rintro (rfl | ⟨hc, hlt⟩)
      · exact ⟨Finset.orderEmbOfFin_mem _ _ _, bs.lt_iff_lt.2 (Fin.lt_def.2 (by simp))⟩
      · exact ⟨hc, lt_trans (bs.lt_iff_lt.2 (Fin.lt_def.2 (by simp))) hlt⟩
  unfold nAbove
  rw [hfilter, Finset.card_insert_of_notMem (by simp)]

theorem nAbove_last (j : Fin (Bset m).card) (h : ¬ j.val + 1 < (Bset m).card) :
    nAbove m ((Bset m).orderEmbOfFin rfl j) = 0 := by
  unfold nAbove
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc hlt
  obtain ⟨i, rfl⟩ := exists_orderEmb_eq m c hc
  have h1 := ((Bset m).orderEmbOfFin rfl).lt_iff_lt.1 hlt
  rw [Fin.lt_def] at h1
  have h2 := i.isLt
  omega

/-- A root of `R` in `(b_j, b_{j+1})`, or in `(b_r, ∞)` for the last index. -/
theorem exists_root (j : Fin (Bset m).card) :
    ∃ τ : ℝ, aeval τ (secular m) = 0 ∧ (((Bset m).orderEmbOfFin rfl j : ℕ) : ℝ) < τ ∧
      ∀ h : j.val + 1 < (Bset m).card,
        τ < (((Bset m).orderEmbOfFin rfl ⟨j.val + 1, h⟩ : ℕ) : ℝ) := by
  set bs := (Bset m).orderEmbOfFin rfl with hbs
  have hcont : Continuous fun t : ℝ => aeval t (secular m) := Polynomial.continuous_aeval _
  have h1 : (-1 : ℝ) ^ nAbove m (bs j) * aeval ((bs j : ℕ) : ℝ) (secular m) < 0 :=
    sign_aeval_secular_of_mem m _ (Finset.orderEmbOfFin_mem _ _ _)
  by_cases h : j.val + 1 < (Bset m).card
  · have h2 : (-1 : ℝ) ^ nAbove m (bs ⟨j.val + 1, h⟩) *
        aeval ((bs ⟨j.val + 1, h⟩ : ℕ) : ℝ) (secular m) < 0 :=
      sign_aeval_secular_of_mem m _ (Finset.orderEmbOfFin_mem _ _ _)
    rw [nAbove_succ m j h, pow_succ] at h1
    have hs0 : (-1 : ℝ) ^ nAbove m (bs ⟨j.val + 1, h⟩) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hle : ((bs j : ℕ) : ℝ) ≤ ((bs ⟨j.val + 1, h⟩ : ℕ) : ℝ) := by
      exact_mod_cast (bs.lt_iff_lt.2 (Fin.lt_def.2 (by simp))).le
    have hmem : (0 : ℝ) ∈ Set.Ioo
        ((fun t : ℝ => (-1 : ℝ) ^ nAbove m (bs ⟨j.val + 1, h⟩) * aeval t (secular m))
          ((bs ⟨j.val + 1, h⟩ : ℕ) : ℝ))
        ((fun t : ℝ => (-1 : ℝ) ^ nAbove m (bs ⟨j.val + 1, h⟩) * aeval t (secular m))
          ((bs j : ℕ) : ℝ)) := by
      simp only [Set.mem_Ioo]
      constructor <;> linarith
    obtain ⟨τ, ⟨hτ1, hτ2⟩, hτ⟩ :=
      intermediate_value_Ioo' hle (continuous_const.mul hcont).continuousOn hmem
    refine ⟨τ, ?_, hτ1, fun _ => hτ2⟩
    exact (mul_eq_zero.1 hτ).resolve_left hs0
  · rw [nAbove_last m j h, pow_zero, one_mul] at h1
    have hT : 0 < aeval ((bstar m : ℝ) + Multiset.card m + 1) (secular m) :=
      aeval_secular_pos m _ (by linarith)
    have hle : ((bs j : ℕ) : ℝ) ≤ (bstar m : ℝ) + Multiset.card m + 1 := by
      have h3 : bs j ≤ bstar m := Finset.le_sup (f := id) (Finset.orderEmbOfFin_mem _ _ _)
      have h4 : ((bs j : ℕ) : ℝ) ≤ bstar m := by exact_mod_cast h3
      have h5 : (0 : ℝ) ≤ Multiset.card m := Nat.cast_nonneg _
      linarith
    obtain ⟨τ, ⟨hτ1, _⟩, hτ⟩ :=
      intermediate_value_Ioo hle hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨h1, hT⟩)
    exact ⟨τ, hτ, hτ1, fun h' => absurd h' h⟩

/-- Lemma 3.1(i), numerical part: the roots `t_1 < ⋯ < t_r` of `R`, their position relative to
`B`, and the equality of the root multiset of `R` (over `ℝ`) with `{t_1, …, t_r}`. -/
theorem roots_spec (hm : m ≠ 0) :
    ∃ t : Fin (Bset m).card → ℝ, StrictMono t ∧
      ((secular m).map (Int.castRingHom ℝ)).roots = Multiset.map t Finset.univ.val ∧
      (∀ j, (((Bset m).orderEmbOfFin rfl j : ℕ) : ℝ) < t j) ∧
      (∀ (j : Fin (Bset m).card) (h : j.val + 1 < (Bset m).card),
        t j < (((Bset m).orderEmbOfFin rfl ⟨j.val + 1, h⟩ : ℕ) : ℝ)) ∧
      (∀ j, 0 < t j ∧ ∀ b ∈ Bset m, t j ≠ (b : ℝ)) ∧
      (∀ j, aeval (t j) (secular m) = 0) := by
  choose t hR hlo hhi using exists_root m
  set bs := (Bset m).orderEmbOfFin rfl with hbs
  have hmono : StrictMono t := by
    intro i j hij
    rw [Fin.lt_def] at hij
    have h : i.val + 1 < (Bset m).card := by
      have := j.isLt
      omega
    have h3 : bs ⟨i.val + 1, h⟩ ≤ bs j := bs.le_iff_le.2 (Fin.le_def.2 (by simp only; omega))
    have h4 : ((bs ⟨i.val + 1, h⟩ : ℕ) : ℝ) ≤ ((bs j : ℕ) : ℝ) := by exact_mod_cast h3
    linarith [hhi i h, hlo j]
  refine ⟨t, hmono, ?_, hlo, hhi, ?_, hR⟩
  · have hmon := secular_monic m hm
    have hne : (secular m).map (Int.castRingHom ℝ) ≠ 0 := (hmon.1.map _).ne_zero
    symm
    apply Multiset.eq_of_le_of_card_le
    · rw [Multiset.le_iff_subset (Multiset.Nodup.map hmono.injective Finset.univ.nodup)]
      intro x hx
      obtain ⟨j, _, rfl⟩ := Multiset.mem_map.1 hx
      rw [mem_roots hne, IsRoot.def, eval_map_secular]
      exact hR j
    · rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
      calc Multiset.card ((secular m).map (Int.castRingHom ℝ)).roots
          ≤ ((secular m).map (Int.castRingHom ℝ)).natDegree := card_roots' _
        _ = (Bset m).card := by rw [hmon.1.natDegree_map, hmon.2]
  · intro j
    refine ⟨lt_of_le_of_lt (Nat.cast_nonneg _) (hlo j), ?_⟩
    intro b hb heq
    obtain ⟨i, rfl⟩ := exists_orderEmb_eq m b hb
    rcases lt_or_ge j i with hji | hij
    · rw [Fin.lt_def] at hji
      have h : j.val + 1 < (Bset m).card := by
        have := i.isLt
        omega
      have h3 : bs ⟨j.val + 1, h⟩ ≤ bs i := bs.le_iff_le.2 (Fin.le_def.2 (by simp only; omega))
      have h4 : ((bs ⟨j.val + 1, h⟩ : ℕ) : ℝ) ≤ ((bs i : ℕ) : ℝ) := by exact_mod_cast h3
      linarith [hhi j h]
    · have h3 : bs i ≤ bs j := bs.le_iff_le.2 hij
      have h4 : ((bs i : ℕ) : ℝ) ≤ ((bs j : ℕ) : ℝ) := by exact_mod_cast h3
      linarith [hlo j]

end

end P8Spec
