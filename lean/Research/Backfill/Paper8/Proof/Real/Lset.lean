import Research.Backfill.Paper8.Challenge

/-!
# Paper 8, Lemma 4.1 (realizable leaf sums)

`Lset β k` is described exactly and its size computed. The forward inclusion bounds the sum
pointwise. The backward inclusion uses `M = (kβ - Λ)/2` leaves of sign `-1`, distributed as
`m_i = min β (M - 1 - β i) + [i = M / β]` (fill the branches in order with `M - 1` leaves, then
add one leaf at branch `M / β`), and `λ_i = β - 2 m_i`. The size is that of the image of
`range (N + 1)` under `j ↦ N - 2j`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge

namespace P8Real

/-! ### The forward inclusion -/

/-- A sum bounded pointwise, with a smaller bound at one index. -/
theorem sum_le_aux {k : ℕ} (f : Fin k → ℤ) (c d : ℤ) (j0 : Fin k)
    (h : ∀ j, f j ≤ c - if j = j0 then d else 0) : ∑ j, f j ≤ k * c - d := by
  calc ∑ j, f j ≤ ∑ j, (c - if j = j0 then d else 0) := Finset.sum_le_sum fun j _ => h j
    _ = k * c - d := by simp [Finset.sum_sub_distrib]

theorem lset_parity {β k : ℕ} {Λ : ℤ} (h : Λ ∈ Lset β k) : Even (Λ - (k : ℤ) * β) := by
  obtain ⟨l, hl, hsum, -, -⟩ := h
  have : Λ - (k : ℤ) * β = ∑ i, (l i - (β : ℤ)) := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  rw [this]
  exact Finset.even_sum _ fun i _ => (hl i).2

theorem lset_abs_le {β k : ℕ} {Λ : ℤ} (h : Λ ∈ Lset β k) (hβ : 2 ≤ β) :
    |Λ| ≤ (k : ℤ) * β - 2 := by
  obtain ⟨l, hl, hsum, -, hsmall⟩ := h
  obtain ⟨i0, hi0⟩ := hsmall hβ
  have h0 := hl i0
  rw [abs_lt] at hi0
  rw [abs_le, Int.even_iff] at h0
  have hup : ∀ j, l j ≤ (β : ℤ) - if j = i0 then 2 else 0 := by
    intro j
    have hj := hl j
    rw [abs_le] at hj
    by_cases hji : j = i0
    · subst hji; simp only [ite_true]; omega
    · simp only [hji, ite_false]; omega
  have hlo : ∀ j, -l j ≤ (β : ℤ) - if j = i0 then 2 else 0 := by
    intro j
    have hj := hl j
    rw [abs_le] at hj
    by_cases hji : j = i0
    · subst hji; simp only [ite_true]; omega
    · simp only [hji, ite_false]; omega
  have h1 := sum_le_aux l _ _ i0 hup
  have h2 := sum_le_aux (fun j => -l j) _ _ i0 hlo
  rw [Finset.sum_neg_distrib] at h2
  rw [abs_le]
  constructor <;> linarith

theorem lset_abs_le_one {k : ℕ} {Λ : ℤ} (h : Λ ∈ Lset 1 k) (hk : 2 ≤ k) :
    |Λ| ≤ (k : ℤ) - 2 := by
  obtain ⟨l, hl, hsum, hne, -⟩ := h
  have hval : ∀ j, l j = 1 ∨ l j = -1 := by
    intro j
    have hj := hl j
    rw [abs_le, Int.even_iff] at hj
    omega
  obtain ⟨i, i', hii'⟩ := hne hk
  -- an index with value `1` and one with value `-1`
  obtain ⟨ip, im, hip, him⟩ : ∃ ip im, l ip = 1 ∧ l im = -1 := by
    rcases hval i with h1 | h1 <;> rcases hval i' with h2 | h2
    · exact absurd (h1.trans h2.symm) hii'
    · exact ⟨i, i', h1, h2⟩
    · exact ⟨i', i, h2, h1⟩
    · exact absurd (h1.trans h2.symm) hii'
  have hup : ∀ j, l j ≤ (1 : ℤ) - if j = im then 2 else 0 := by
    intro j
    by_cases hj : j = im
    · subst hj; simp only [ite_true]; omega
    · simp only [hj, ite_false]; rcases hval j with h | h <;> omega
  have hlo : ∀ j, -l j ≤ (1 : ℤ) - if j = ip then 2 else 0 := by
    intro j
    by_cases hj : j = ip
    · subst hj; simp only [ite_true]; omega
    · simp only [hj, ite_false]; rcases hval j with h | h <;> omega
  have h1 := sum_le_aux l _ _ im hup
  have h2 := sum_le_aux (fun j => -l j) _ _ ip hlo
  rw [Finset.sum_neg_distrib] at h2
  rw [abs_le]
  constructor <;> linarith

theorem zero_not_mem_lset_two_two : (0 : ℤ) ∉ Lset 2 2 := by
  rintro ⟨l, hl, hsum, hne, hsmall⟩
  obtain ⟨i0, hi0⟩ := hsmall le_rfl
  have hval : ∀ j, l j = 2 ∨ l j = 0 ∨ l j = -2 := by
    intro j
    have hj := hl j
    rw [abs_le, Int.even_iff] at hj
    push_cast at hj
    omega
  have h0 : l i0 = 0 := by
    rw [abs_lt] at hi0
    push_cast at hi0
    rcases hval i0 with h | h | h <;> omega
  rw [Fin.sum_univ_two] at hsum
  obtain ⟨i, i', hii'⟩ := hne le_rfl
  have hall : ∀ j, l j = 0 := by
    have : l 0 = 0 ∧ l 1 = 0 := by
      fin_cases i0
      · simp only [Fin.zero_eta] at h0; omega
      · simp only [Fin.mk_one] at h0; omega
    intro j
    fin_cases j
    · exact this.1
    · exact this.2
  exact hii' ((hall i).trans (hall i').symm)

/-! ### The backward inclusion -/

theorem sum_min_fill (β N n : ℕ) :
    ∑ i ∈ Finset.range n, min β (N - β * i) = min N (β * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ]
    omega

/-- The number of leaves of sign `-1` on branch `i`: fill with `M - 1` leaves, then one more at
branch `M / β`. -/
def fillM (β M i : ℕ) : ℕ := min β (M - 1 - β * i) + if i = M / β then 1 else 0

theorem sum_fillM (β k M : ℕ) (hβ : 1 ≤ β) (hM : 1 ≤ M) (hMk : M < k * β) :
    ∑ i ∈ Finset.range k, fillM β M i = M := by
  have hq : M / β < k := (Nat.div_lt_iff_lt_mul (by omega)).2 hMk
  unfold fillM
  rw [Finset.sum_add_distrib, sum_min_fill, Finset.sum_ite_eq']
  simp only [Finset.mem_range, hq, ite_true]
  rw [Nat.mul_comm] at hMk
  omega

theorem fillM_le (β M i : ℕ) (hβ : 1 ≤ β) : fillM β M i ≤ β := by
  unfold fillM
  have h1 := Nat.div_add_mod M β
  have h2 := Nat.mod_lt M (show 0 < β by omega)
  by_cases hi : i = M / β
  · subst hi
    simp only [ite_true]
    omega
  · simp only [hi, ite_false]
    omega

/-- At branch `q = M / β`: `1 ≤ m_q` and `m_q ≤ β - 1` when `β ≥ 2`. -/
theorem fillM_q (β M : ℕ) (hβ : 1 ≤ β) :
    1 ≤ fillM β M (M / β) ∧ (2 ≤ β → fillM β M (M / β) ≤ β - 1) := by
  unfold fillM
  have h1 := Nat.div_add_mod M β
  have h2 := Nat.mod_lt M (show 0 < β by omega)
  simp only [ite_true]
  omega

/-- After branch `q = M / β` there are no leaves of sign `-1`. -/
theorem fillM_gt (β M i : ℕ) (hβ : 1 ≤ β) (hi : M / β < i) : fillM β M i = 0 := by
  unfold fillM
  have h1 := Nat.div_add_mod M β
  have h2 := Nat.mod_lt M (show 0 < β by omega)
  have h3 : β * (M / β + 1) ≤ β * i := Nat.mul_le_mul_left β hi
  rw [Nat.mul_succ] at h3
  have hne : i ≠ M / β := by omega
  simp only [hne, ite_false]
  omega

/-- Branch `0` when `q = M / β ≥ 1`. -/
theorem fillM_zero (β M : ℕ) (hq : 1 ≤ M / β) : fillM β M 0 = min β (M - 1) := by
  unfold fillM
  have hne : (0 : ℕ) ≠ M / β := by omega
  simp only [hne, ite_false, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]

/-- Branch `q - 1` when `β = 1`. -/
theorem fillM_one_pred (M : ℕ) (hM : 1 ≤ M) : fillM 1 M (M - 1) = 0 := by
  unfold fillM
  have hne : M - 1 ≠ M / 1 := by rw [Nat.div_one]; omega
  simp only [hne, ite_false]
  omega

theorem mem_Lset_of (β k : ℕ) (hβ : 1 ≤ β) (hk : 1 ≤ k) (Λ : ℤ)
    (hpar : Even (Λ - (k : ℤ) * β)) (habs : |Λ| ≤ (k : ℤ) * β - 2)
    (hex : ¬ (β = 2 ∧ k = 2 ∧ Λ = 0)) : Λ ∈ Lset β k := by
  obtain ⟨r, hr⟩ := hpar
  rw [abs_le] at habs
  obtain ⟨hlo, hhi⟩ := habs
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = -r := ⟨(-r).toNat, Int.toNat_of_nonneg (by linarith)⟩
  have hkβ : ((k * β : ℕ) : ℤ) = (k : ℤ) * β := by push_cast; ring
  have hM1 : 1 ≤ M := by
    have : (1 : ℤ) ≤ M := by linarith
    exact_mod_cast this
  have hMk : M < k * β := by
    have : (M : ℤ) < ((k * β : ℕ) : ℤ) := by rw [hkβ]; linarith
    exact_mod_cast this
  have hq : M / β < k := (Nat.div_lt_iff_lt_mul (by omega)).2 hMk
  refine ⟨fun i => (β : ℤ) - 2 * (fillM β M i.val : ℤ), ?_, ?_, ?_, ?_⟩
  · -- values in `{-β, …, β}`
    intro i
    have := fillM_le β M i.val hβ
    dsimp only
    refine ⟨?_, ?_⟩
    · rw [abs_le]
      constructor <;> omega
    · rw [Int.even_iff]
      omega
  · -- the sum
    have hs := sum_fillM β k M hβ hM1 hMk
    have hs' : ∑ i ∈ Finset.range k, (fillM β M i : ℤ) = M := by exact_mod_cast hs
    rw [Fin.sum_univ_eq_sum_range (fun i => (β : ℤ) - 2 * (fillM β M i : ℤ)) k,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hs']
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linarith
  · -- not all equal
    intro hk2
    suffices hsuff : ∃ i i' : Fin k, fillM β M i.val ≠ fillM β M i'.val by
      obtain ⟨i, i', hne⟩ := hsuff
      refine ⟨i, i', fun heq => hne ?_⟩
      dsimp only at heq
      have : (fillM β M i.val : ℤ) = fillM β M i'.val := by linarith
      exact_mod_cast this
    have h1 := Nat.div_add_mod M β
    have h2 := Nat.mod_lt M (show 0 < β by omega)
    obtain ⟨hq1, hq2⟩ := fillM_q β M hβ
    by_cases hA : M / β + 1 < k
    · refine ⟨⟨M / β, hq⟩, ⟨M / β + 1, hA⟩, ?_⟩
      dsimp only
      rw [fillM_gt β M (M / β + 1) hβ (by omega)]
      omega
    · have hqpos : 1 ≤ M / β := by omega
      have hz := fillM_zero β M hqpos
      by_cases hB : β = 1
      · subst hB
        have hMq : M / 1 = M := Nat.div_one M
        refine ⟨⟨M - 1, by omega⟩, ⟨M / 1, hq⟩, ?_⟩
        dsimp only
        rw [fillM_one_pred M hM1]
        omega
      · by_cases hC : β ≤ M - 1
        · refine ⟨⟨0, by omega⟩, ⟨M / β, hq⟩, ?_⟩
          have := hq2 (by omega)
          dsimp only
          rw [hz]
          omega
        · -- here `M = β`, `M / β = 1` and `k = 2`
          have hMβ : M = β := by
            have : β * 1 ≤ β * (M / β) := Nat.mul_le_mul_left β hqpos
            omega
          have hq1' : M / β = 1 := by rw [hMβ]; exact Nat.div_self (by omega)
          have hk2' : k = 2 := by omega
          refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
          have e1 : fillM β M 1 = 1 := by
            unfold fillM
            simp only [hq1', ite_true]
            omega
          dsimp only
          rw [hz, e1]
          intro heq
          apply hex
          refine ⟨by omega, hk2', ?_⟩
          have hMβ' : (M : ℤ) = β := by exact_mod_cast hMβ
          subst hk2'
          have hβ2 : (β : ℤ) = 2 := by omega
          push_cast at hr
          nlinarith
  · -- some `|λ_i| < β`
    intro hβ2
    refine ⟨⟨M / β, hq⟩, ?_⟩
    obtain ⟨hq1, hq2⟩ := fillM_q β M hβ
    have := hq2 hβ2
    dsimp only
    rw [abs_lt]
    constructor <;> omega

/-! ### Counting -/

theorem ncard_prog (N : ℕ) : {Λ : ℤ | Even (Λ - N) ∧ |Λ| ≤ N}.ncard = N + 1 := by
  have hset : {Λ : ℤ | Even (Λ - N) ∧ |Λ| ≤ N} =
      ((Finset.range (N + 1)).image (fun j : ℕ => (N : ℤ) - 2 * j) : Set ℤ) := by
    ext Λ
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
      Set.mem_Iio]
    constructor
    · rintro ⟨⟨r, hr⟩, habs⟩
      rw [abs_le] at habs
      obtain ⟨hlo, hhi⟩ := habs
      obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = -r := ⟨(-r).toNat, Int.toNat_of_nonneg (by linarith)⟩
      refine ⟨j, ?_, ?_⟩
      · have : (j : ℤ) < N + 1 := by linarith
        exact_mod_cast this
      · linarith
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨-(j : ℤ), by ring⟩, ?_⟩
      rw [abs_le]
      constructor <;> omega
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective, Finset.card_range]
  intro x y hxy
  simp only at hxy
  omega

theorem lemma_4_1 : Lemma_4_1 := by
  intro β k hβ hk
  refine ⟨fun hβ2 => ?_, fun hβ1 hk2 => ?_, fun hβ1 hk1 => ?_⟩
  · have hset : Lset β k = {Λ : ℤ | Even (Λ - (k : ℤ) * β) ∧ |Λ| ≤ (k : ℤ) * β - 2 ∧
        ¬ (β = 2 ∧ k = 2 ∧ Λ = 0)} := by
      ext Λ
      constructor
      · intro h
        refine ⟨lset_parity h, lset_abs_le h hβ2, ?_⟩
        rintro ⟨rfl, rfl, rfl⟩
        exact zero_not_mem_lset_two_two h
      · rintro ⟨h1, h2, h3⟩
        exact mem_Lset_of β k hβ hk Λ h1 h2 h3
    refine ⟨hset, ?_⟩
    rw [hset]
    by_cases hex : β = 2 ∧ k = 2
    · obtain ⟨rfl, rfl⟩ := hex
      have : {Λ : ℤ | Even (Λ - ((2 : ℕ) : ℤ) * ((2 : ℕ) : ℤ)) ∧
          |Λ| ≤ ((2 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) - 2 ∧ ¬ (2 = 2 ∧ 2 = 2 ∧ Λ = 0)} = {2, -2} := by
        ext Λ
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Int.even_iff,
          abs_le, true_and]
        push_cast
        omega
      rw [this, Set.ncard_pair (by norm_num)]
      rfl
    · have hkβ : 2 ≤ k * β := by nlinarith
      have hN : ((k * β - 2 : ℕ) : ℤ) = (k : ℤ) * β - 2 := by
        rw [Nat.cast_sub hkβ]
        push_cast
        ring
      have : {Λ : ℤ | Even (Λ - (k : ℤ) * β) ∧ |Λ| ≤ (k : ℤ) * β - 2 ∧
          ¬ (β = 2 ∧ k = 2 ∧ Λ = 0)} =
          {Λ : ℤ | Even (Λ - ((k * β - 2 : ℕ) : ℤ)) ∧ |Λ| ≤ ((k * β - 2 : ℕ) : ℤ)} := by
        ext Λ
        simp only [Set.mem_ofPred_eq, hN, Int.even_iff]
        constructor
        · rintro ⟨h1, h2, -⟩
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨by omega, h2, fun h => hex ⟨h.1, h.2.1⟩⟩
      rw [this, ncard_prog]
      simp only [hex, ite_false]
      omega
  · subst hβ1
    have hset : Lset 1 k = {Λ : ℤ | Even (Λ - (k : ℤ)) ∧ |Λ| ≤ (k : ℤ) - 2} := by
      ext Λ
      constructor
      · intro h
        have hp := lset_parity h
        push_cast at hp
        rw [mul_one] at hp
        exact ⟨hp, lset_abs_le_one h hk2⟩
      · rintro ⟨h1, h2⟩
        refine mem_Lset_of 1 k le_rfl hk Λ (by push_cast; rw [mul_one]; exact h1)
          (by push_cast; rw [mul_one]; exact h2) (by omega)
    refine ⟨hset, ?_⟩
    rw [hset]
    have hN : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by
      rw [Nat.cast_sub hk2]
      push_cast
      ring
    have : {Λ : ℤ | Even (Λ - (k : ℤ)) ∧ |Λ| ≤ (k : ℤ) - 2} =
        {Λ : ℤ | Even (Λ - ((k - 2 : ℕ) : ℤ)) ∧ |Λ| ≤ ((k - 2 : ℕ) : ℤ)} := by
      ext Λ
      simp only [Set.mem_ofPred_eq, hN, Int.even_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    rw [this, ncard_prog]
    omega
  · subst hβ1
    subst hk1
    have hset : Lset 1 1 = {1, -1} := by
      ext Λ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨l, hl, hsum, -, -⟩
        rw [Fin.sum_univ_one] at hsum
        have h0 := hl 0
        rw [abs_le, Int.even_iff] at h0
        push_cast at h0
        omega
      · rintro (rfl | rfl)
        · refine ⟨fun _ => 1, fun _ => ⟨by norm_num, by norm_num⟩, by simp, by omega, by omega⟩
        · refine ⟨fun _ => -1, fun _ => ⟨by norm_num, ⟨-1, by norm_num⟩⟩, by simp, by omega, by omega⟩
    refine ⟨hset, ?_⟩
    rw [hset, Set.ncard_pair (by norm_num)]

end P8Real
