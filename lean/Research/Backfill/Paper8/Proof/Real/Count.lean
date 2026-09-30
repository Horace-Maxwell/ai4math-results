import Research.Backfill.Paper8.Challenge

/-!
# Paper 8, Lemma 5.2 (counting non-even pairs)

`r = b* + 1 - g` because `B ⊆ {0, …, b*}`; `sq ≤ ⌊√(b* - 1)⌋` and `sq ≤ g` (the map `q ↦ q²`
is injective into the gaps). For `N_I ≤ sq + 1`: by Lemma 3.3(b) an integer pair is
`{x - q, x + q}` with `R(q²) = 0`; by Lemma 3.1(i) the root `q²` is either the largest root `t_r`
(at most one `|q|`) or lies in `(0, b*)` outside `B`, so `|q|` is counted by `sq`. The last
inequality is Lemma 3.3(d).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Polynomial

namespace P8Real

section Count

theorem bset_subset_range (m : Multiset ℕ) : Bset m ⊆ Finset.range (bstar m + 1) := by
  intro b hb
  have : b ≤ bstar m := Finset.le_sup (f := id) hb
  exact Finset.mem_range.2 (by omega)

/-- `r = b* + 1 - g`. -/
theorem card_bset_eq (m : Multiset ℕ) : (Bset m).card = bstar m + 1 - gapCount m := by
  have h := Finset.card_sdiff_of_subset (bset_subset_range m)
  have h2 := Finset.card_le_card (bset_subset_range m)
  simp only [Finset.card_range] at h h2
  unfold gapCount
  omega

/-- The finset counted by `sq`. -/
def sqSet (B : Finset ℕ) (bs : ℕ) : Finset ℕ :=
  (Finset.Icc 1 bs).filter (fun q => q ^ 2 ≤ bs - 1 ∧ q ^ 2 ∉ B)

theorem sqCountB_eq (B : Finset ℕ) (bs : ℕ) : sqCountB B bs = (sqSet B bs).card := rfl

theorem mem_sqSet {B : Finset ℕ} {bs q : ℕ} :
    q ∈ sqSet B bs ↔ (1 ≤ q ∧ q ≤ bs) ∧ q ^ 2 ≤ bs - 1 ∧ q ^ 2 ∉ B := by
  simp [sqSet]

/-- `sq ≤ ⌊√(b* - 1)⌋`. -/
theorem sq_le_sqrt (B : Finset ℕ) (bs : ℕ) : sqCountB B bs ≤ Nat.sqrt (bs - 1) := by
  have hsub : sqSet B bs ⊆ Finset.Icc 1 (Nat.sqrt (bs - 1)) := by
    intro q hq
    rw [mem_sqSet] at hq
    rw [Finset.mem_Icc]
    exact ⟨hq.1.1, Nat.le_sqrt'.2 hq.2.1⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  rw [sqCountB_eq]
  omega

/-- `sq ≤ g`. -/
theorem sq_le_gap (m : Multiset ℕ) : sqCountB (Bset m) (bstar m) ≤ gapCount m := by
  rw [sqCountB_eq]
  unfold gapCount
  apply Finset.card_le_card_of_injOn (fun q => q ^ 2)
  · intro q hq
    rw [Finset.mem_coe, mem_sqSet] at hq
    simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_range]
    exact ⟨by omega, hq.2.2⟩
  · intro q _ q' _ h
    exact Nat.pow_left_injective (by norm_num) h

/-- An integer root `q²` of `R` is the largest root of `R`, or `q ≠ 0`, `q² < b*` and
`q² ∉ B` (Lemma 3.1(i)). -/
theorem int_sq_root (h31 : Lemma_3_1_i) {k : ℕ} (a : Fin k → ℕ) (hk : 0 < k) :
    ∃ t : Fin (Bset (branchMS a)).card → ℝ,
      ∀ q : ℤ, (secular (branchMS a)).eval (q ^ 2) = 0 →
        (∃ j : Fin (Bset (branchMS a)).card, j.val + 1 = (Bset (branchMS a)).card ∧
          t j = (q : ℝ) ^ 2) ∨
        (q ≠ 0 ∧ q ^ 2 < (bstar (branchMS a) : ℤ) ∧ ∀ b ∈ Bset (branchMS a), (b : ℤ) ≠ q ^ 2) := by
  have H := h31 k a hk
  dsimp only at H
  obtain ⟨t, -, hroots, -, hupp, hpos, -⟩ := H
  refine ⟨t, ?_⟩
  have hr1 : 1 ≤ (Bset (branchMS a)).card := by
    apply Finset.card_pos.2
    refine ⟨a ⟨0, hk⟩, ?_⟩
    simp [Bset, branchMS]
  have hp0 : (secular (branchMS a)).map (Int.castRingHom ℝ) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.roots_zero] at hroots
    have := congrArg Multiset.card hroots
    simp at this
    omega
  intro q hq
  have hmem : ((q ^ 2 : ℤ) : ℝ) ∈ ((secular (branchMS a)).map (Int.castRingHom ℝ)).roots := by
    rw [Polynomial.mem_roots hp0, Polynomial.IsRoot, Polynomial.eval_intCast_map]
    simp [hq]
  rw [hroots, Multiset.mem_map] at hmem
  obtain ⟨j, -, hj⟩ := hmem
  push_cast at hj
  by_cases hlast : j.val + 1 = (Bset (branchMS a)).card
  · exact Or.inl ⟨j, hlast, hj⟩
  · right
    have hlt : j.val + 1 < (Bset (branchMS a)).card := by omega
    have h1 := hupp j hlt
    have hbmem := Finset.orderEmbOfFin_mem (Bset (branchMS a)) rfl ⟨j.val + 1, hlt⟩
    have h2 : (Bset (branchMS a)).orderEmbOfFin rfl ⟨j.val + 1, hlt⟩ ≤ bstar (branchMS a) :=
      Finset.le_sup (f := id) hbmem
    obtain ⟨hpj, hnb⟩ := hpos j
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl
      simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hj
      linarith
    · have h3 : (q : ℝ) ^ 2 < (bstar (branchMS a) : ℝ) := by
        rw [← hj]
        calc t j < _ := h1
          _ ≤ _ := by exact_mod_cast h2
      exact_mod_cast h3
    · intro b hb hbq
      apply hnb b hb
      rw [hj]
      exact_mod_cast hbq.symm

/-- `N_I ≤ sq + 1`. -/
theorem NI_le (h31 : Lemma_3_1_i) (h33b : Lemma_3_3_b) {k : ℕ} (a : Fin k → ℕ) (hk : 0 < k) :
    NI (branchMS a) ≤ sqCountB (Bset (branchMS a)) (bstar (branchMS a)) + 1 := by
  obtain ⟨t, key⟩ := int_sq_root h31 a hk
  set S : Set ℕ := (sqSet (Bset (branchMS a)) (bstar (branchMS a)) : Set ℕ) with hS
  set E : Set ℕ := {n | ∃ j : Fin (Bset (branchMS a)).card, j.val + 1 = (Bset (branchMS a)).card ∧
    t j = (n : ℝ) ^ 2}
  set ψ : ℕ → Set ℚ[X] := fun n => {X - C (n : ℚ), X + C (n : ℚ)} with hψ
  have hsub : {P ∈ nonEvenPairs (branchMS a) | ∀ f ∈ P, f.natDegree = 1} ⊆ ψ '' (S ∪ E) := by
    rintro P ⟨⟨f, hf, hne, rfl⟩, hdeg⟩
    have hdeg1 : f.natDegree = 1 := hdeg f (Set.mem_insert _ _)
    obtain ⟨-, -, -, hroot⟩ := h33b k a hk f hf hne
    have hfX : f = X + C (f.coeff 0) := hf.1.eq_X_add_C hdeg1
    have hθ : aeval (-(f.coeff 0 : ℝ)) f = 0 := by
      rw [hfX]
      simp
    obtain ⟨-, hint, -⟩ := hroot _ hθ
    obtain ⟨q, hq, hRq⟩ := hint hdeg1
    have hc : f.coeff 0 = -(q : ℚ) := by
      have : ((f.coeff 0 : ℚ) : ℝ) = ((-(q : ℚ) : ℚ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hf' : f = X - C (q : ℚ) := by rw [hfX, hc, map_neg, ← sub_eq_add_neg]
    have hmir : BackfillPaper8.Challenge.mirror f = X + C (q : ℚ) := by
      rw [hf', BackfillPaper8.Challenge.mirror, natDegree_X_sub_C, sub_comp, X_comp, C_comp]
      simp only [pow_one, map_neg, map_one]
      ring
    refine ⟨q.natAbs, ?_, ?_⟩
    · rcases key q hRq with ⟨j, hj, htj⟩ | ⟨hq0, hlt, hnb⟩
      · right
        refine ⟨j, hj, ?_⟩
        rw [htj]
        simp [sq_abs]
      · left
        rw [hS, Finset.mem_coe, mem_sqSet]
        have hn2 : ((q.natAbs ^ 2 : ℕ) : ℤ) = q ^ 2 := by push_cast; exact sq_abs q
        have hn1 : 1 ≤ q.natAbs := Int.natAbs_pos.2 hq0
        have hlt' : q.natAbs ^ 2 < bstar (branchMS a) := by
          have : ((q.natAbs ^ 2 : ℕ) : ℤ) < (bstar (branchMS a) : ℤ) := by rw [hn2]; exact hlt
          exact_mod_cast this
        have hle : q.natAbs ≤ q.natAbs ^ 2 := by nlinarith
        refine ⟨⟨hn1, by omega⟩, by omega, ?_⟩
        intro hin
        exact hnb _ hin hn2
    · rw [hψ]
      dsimp only
      rw [hmir, hf']
      obtain ⟨n, hn⟩ : ∃ n : ℕ, n = q.natAbs := ⟨_, rfl⟩
      rw [← hn]
      rcases Int.natAbs_eq q with h | h
      · rw [← hn] at h
        have hqn : (q : ℚ) = (n : ℚ) := by rw [h, Int.cast_natCast]
        rw [hqn]
      · rw [← hn] at h
        have hqn : (q : ℚ) = -(n : ℚ) := by rw [h, Int.cast_neg, Int.cast_natCast]
        rw [hqn, map_neg, sub_neg_eq_add, ← sub_eq_add_neg, Set.pair_comm]
  have hEsub : E.Subsingleton := by
    rintro n ⟨j, hj, htj⟩ n' ⟨j', hj', htj'⟩
    have hjj : j = j' := Fin.ext (by omega)
    subst hjj
    have h1 : ((n ^ 2 : ℕ) : ℝ) = ((n' ^ 2 : ℕ) : ℝ) := by
      push_cast
      exact htj.symm.trans htj'
    have h2 : n ^ 2 = n' ^ 2 := by exact_mod_cast h1
    exact Nat.pow_left_injective (by norm_num) h2
  have hSfin : S.Finite := Finset.finite_toSet _
  have hEfin : E.Finite := hEsub.finite
  have hEcard : E.ncard ≤ 1 := (Set.ncard_le_one hEfin).2 (fun x hx y hy => hEsub hx hy)
  have hfin : (ψ '' (S ∪ E)).Finite := (hSfin.union hEfin).image _
  calc NI (branchMS a) = ({P ∈ nonEvenPairs (branchMS a) | ∀ f ∈ P, f.natDegree = 1}).ncard := rfl
    _ ≤ (ψ '' (S ∪ E)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (S ∪ E).ncard := Set.ncard_image_le (hSfin.union hEfin)
    _ ≤ S.ncard + E.ncard := Set.ncard_union_le _ _
    _ ≤ sqCountB (Bset (branchMS a)) (bstar (branchMS a)) + 1 := by
      rw [hS, Set.ncard_coe_finset, ← sqCountB_eq]
      omega

/-- **Lemma 5.2**, from Lemmas 3.1(i), 3.3(b) and 3.3(d). -/
theorem lemma_5_2 (h31 : Lemma_3_1_i) (h33b : Lemma_3_3_b) (h33d : Lemma_3_3_d) : Lemma_5_2 := by
  intro k a hk _
  exact ⟨card_bset_eq _, sq_le_sqrt _ _, sq_le_gap _, NI_le h31 h33b a hk, (h33d k a hk).2.2⟩

end Count

end P8Real
