import Research.Backfill.Paper3.Proof.TS.Code
import Research.Backfill.Paper3.Proof.Basic

/-!
# `N_{≤t}` of coded graphs by bit masks

A vertex set `A ⊆ Fin n` is encoded by its bit mask `mask A = Σ_{i ∈ A} 2^i`; `eMask n c m`
counts the edges of `ofCode n c` inside the mask `m`. Then `iCount (ofCode n c) t` is the number
of masks `m < 2^n` with `eMask n c m ≤ t`. The kernel computes the whole histogram of `eMask` at
once as the number `polyH n c = Σ_{m < 2^n} 2048^(eMask n c m)` (the edge polynomial at `2048`),
compared with the base-2048 number `ofD N` of a claimed histogram `N`; `iCount_ofCode_eq` reads
off `N_{≤t}` from `N`.
-/

set_option autoImplicit false

namespace P3TS

open Finset BackfillPaper3.Challenge

/-- `Σ_{k < n} f k`, by primitive recursion (for the kernel). -/
def sumLt (n : ℕ) (f : ℕ → ℕ) : ℕ := Nat.rec 0 (fun k acc => acc + f k) n

theorem sumLt_eq (n : ℕ) (f : ℕ → ℕ) : sumLt n f = ∑ k ∈ range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_range_succ, ← ih]; rfl

/-- The number of edges of `ofCode n c` inside the vertex set with bit mask `m`. -/
def eMask (n c m : ℕ) : ℕ :=
  sumLt n fun v =>
    if m.testBit v then sumLt v (fun u => if m.testBit u && adjB n c u v then 1 else 0) else 0

/-- A symmetric double sum with zero diagonal is twice the sum over `a < b`. -/
theorem sum_sum_sym (N : ℕ) (g : ℕ → ℕ → ℕ) (hs : ∀ a < N, ∀ b < N, g a b = g b a)
    (hd : ∀ a < N, g a a = 0) :
    ∑ a ∈ range N, ∑ b ∈ range N, g a b = 2 * ∑ b ∈ range N, ∑ a ∈ range b, g a b := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ih' := ih (fun a ha b hb => hs a (by omega) b (by omega)) (fun a ha => hd a (by omega))
    have h2 : ∑ b ∈ range N, g N b = ∑ a ∈ range N, g a N :=
      sum_congr rfl fun b hb => hs N (by omega) b (by simp at hb; omega)
    have h3 := hd N (by omega)
    simp only [sum_range_succ, sum_add_distrib]
    rw [ih', h2, h3]
    ring

/-- The bit mask of a vertex set. -/
def mask {n : ℕ} (A : Finset (Fin n)) : ℕ := ∑ i ∈ A, 2 ^ i.val

theorem mask_eq {n : ℕ} (A : Finset (Fin n)) :
    mask A = equivBitIndices.symm (A.map Fin.valEmbedding) := by
  simp [mask, equivBitIndices_symm_apply, sum_map]

theorem testBit_mask {n : ℕ} (A : Finset (Fin n)) (i : ℕ) :
    (mask A).testBit i = true ↔ ∃ j ∈ A, j.val = i := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, ← equivBitIndices_apply, mask_eq,
    Equiv.apply_symm_apply, mem_map]
  simp

theorem testBit_mask_fin {n : ℕ} (A : Finset (Fin n)) (i : Fin n) :
    (mask A).testBit i.val = true ↔ i ∈ A := by
  rw [testBit_mask]
  constructor
  · rintro ⟨j, hj, hji⟩
    rwa [← Fin.ext hji]
  · exact fun h => ⟨i, h, rfl⟩

theorem mask_lt {n : ℕ} (A : Finset (Fin n)) : mask A < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_contra h
  rw [Bool.not_eq_false, testBit_mask] at h
  obtain ⟨j, -, rfl⟩ := h
  exact absurd j.isLt (by omega)

theorem mask_injective {n : ℕ} : Function.Injective (mask (n := n)) := by
  intro A B h
  ext i
  rw [← testBit_mask_fin, ← testBit_mask_fin, h]

/-- Every `m < 2^n` is the mask of the set of its bits. -/
theorem mask_bits {n m : ℕ} (hm : m < 2 ^ n) :
    mask (univ.filter fun i : Fin n => m.testBit i.val = true) = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have := testBit_mask_fin (univ.filter fun i : Fin n => m.testBit i.val = true) ⟨i, hi⟩
    simp only [mem_filter, mem_univ, true_and] at this
    exact Bool.eq_iff_iff.2 this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (mask_lt _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem sum_fin_fin (n : ℕ) (f : ℕ → ℕ → ℕ) :
    ∑ a : Fin n, ∑ b : Fin n, f a.val b.val = ∑ a ∈ range n, ∑ b ∈ range n, f a b := by
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin n, f a b.val) n]
  exact sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (f a) n

/-- `e(A)` of a coded graph is `eMask` of the mask of `A`. -/
theorem edgesIn_ofCode {n c : ℕ} (hwf : wfB n c = true) [DecidableRel (ofCode n c).Adj]
    (A : Finset (Fin n)) : edgesIn (ofCode n c) A = eMask n c (mask A) := by
  let g : ℕ → ℕ → ℕ := fun a b =>
    if adjB n c a b && (mask A).testBit a && (mask A).testBit b then 1 else 0
  have h1 := P3Basic.two_mul_edgesIn (ofCode n c) A
  rw [card_filter, Fintype.sum_prod_type] at h1
  have h2 : ∑ a : Fin n, ∑ b : Fin n,
      (if (ofCode n c).Adj (a, b).1 (a, b).2 ∧ (a, b).1 ∈ A ∧ (a, b).2 ∈ A then 1 else 0) =
      ∑ a : Fin n, ∑ b : Fin n, g a.val b.val := by
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    simp only [g, ofCode_adj hwf, ← testBit_mask_fin A, Bool.and_eq_true, and_assoc]
  rw [h2, sum_fin_fin n g] at h1
  have hsym : ∀ a < n, ∀ b < n, g a b = g b a := by
    intro a ha b hb
    simp only [g, (wfB_spec hwf ha hb).2]
    congr 1
    rw [Bool.and_assoc, Bool.and_assoc, Bool.and_comm ((mask A).testBit a)]
  have hdiag : ∀ a < n, g a a = 0 := by
    intro a ha
    simp [g, (wfB_spec hwf ha ha).1]
  rw [sum_sum_sym n g hsym hdiag] at h1
  have h3 : eMask n c (mask A) = ∑ b ∈ range n, ∑ a ∈ range b, g a b := by
    rw [eMask, sumLt_eq]
    refine sum_congr rfl fun b _ => ?_
    by_cases hb : (mask A).testBit b = true
    · rw [ite_eq_left hb, sumLt_eq]
      refine sum_congr rfl fun a _ => ?_
      simp only [g, hb, Bool.and_true, Bool.and_comm ((mask A).testBit a)]
    · rw [ite_eq_right hb]
      symm
      refine sum_eq_zero fun a _ => ?_
      simp [g, Bool.eq_false_iff.2 hb]
  rw [h3]
  omega

/-- `N_{≤t}` of a coded graph, as a count of bit masks. -/
theorem iCount_ofCode {n c : ℕ} (hwf : wfB n c = true) [DecidableRel (ofCode n c).Adj] (t : ℕ) :
    iCount (ofCode n c) t = #{m ∈ range (2 ^ n) | eMask n c m ≤ t} := by
  unfold iCount
  apply card_bij (fun A _ => mask A)
  · intro A hA
    simp only [mem_filter, mem_univ, true_and] at hA
    simp only [mem_filter, mem_range]
    exact ⟨mask_lt A, (edgesIn_ofCode hwf A) ▸ hA⟩
  · intro A _ B _ h
    exact mask_injective h
  · intro m hm
    simp only [mem_filter, mem_range] at hm
    refine ⟨univ.filter fun i : Fin n => m.testBit i.val = true, ?_, mask_bits hm.1⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [edgesIn_ofCode hwf, mask_bits hm.1]
    exact hm.2

/-- `eMask` is at most `n(n-1)/2`. -/
theorem eMask_le (n c m : ℕ) : eMask n c m ≤ n * (n - 1) / 2 := by
  rw [← sum_range_id, eMask, sumLt_eq]
  refine sum_le_sum fun v _ => ?_
  split_ifs
  · rw [sumLt_eq]
    calc ∑ u ∈ range v, (if m.testBit u && adjB n c u v then 1 else 0)
        ≤ ∑ _u ∈ range v, 1 := sum_le_sum fun u _ => by split_ifs <;> omega
      _ = v := by simp
  · exact Nat.zero_le v

/-- The number `Σ_s N_s 2048^s`. -/
def ofD : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 2048 * ofD xs

theorem ofD_inj : ∀ {L₁ L₂ : List ℕ}, L₁.length = L₂.length → (∀ x ∈ L₁, x < 2048) →
    (∀ x ∈ L₂, x < 2048) → ofD L₁ = ofD L₂ → L₁ = L₂
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, hl, h1, h2, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hx := h1 x List.mem_cons_self
    have hy := h2 y List.mem_cons_self
    simp only [ofD] at h
    have hxy : x = y := by omega
    have hrest : ofD xs = ofD ys := by omega
    rw [hxy, ofD_inj hl (fun z hz => h1 z (List.mem_cons_of_mem x hz))
      (fun z hz => h2 z (List.mem_cons_of_mem y hz)) hrest]

theorem ofD_eq_sum (L : List ℕ) : ofD L = ∑ i ∈ range L.length, L.getD i 0 * 2048 ^ i := by
  induction L with
  | nil => simp [ofD]
  | cons x xs ih =>
    rw [ofD, ih, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [mul_sum, add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    ring

/-- `Σ_{m < 2^n} 2048^(eMask n c m)`: the histogram of `eMask` in base `2048`. -/
def polyH (n c : ℕ) : ℕ := sumLt (2 ^ n) fun m => 2048 ^ eMask n c m

/-- Reading the histogram off `polyH`: if `polyH n c = ofD N` (with `n ≤ 10`, `N` of length
`n(n-1)/2 + 1` with entries `< 2048`), then `N_s` masks have exactly `s` edges. -/
theorem card_eMask_eq {n c : ℕ} (hn : n ≤ 10) {N : List ℕ} (hlen : N.length = n * (n - 1) / 2 + 1)
    (hN : ∀ x ∈ N, x < 2048) (h : polyH n c = ofD N) (s : ℕ) :
    #{m ∈ range (2 ^ n) | eMask n c m = s} = N.getD s 0 := by
  set L := n * (n - 1) / 2 + 1
  have h2n : 2 ^ n < 2048 := lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hn) (by norm_num)
  set C := (List.range L).map fun s => #{m ∈ range (2 ^ n) | eMask n c m = s}
  have hClen : C.length = L := by simp [C]
  have hCget : ∀ s, C.getD s 0 = if s < L then #{m ∈ range (2 ^ n) | eMask n c m = s} else 0 := by
    intro s
    split_ifs with hs
    · rw [List.getD_eq_getElem _ _ (by rw [hClen]; exact hs)]
      simp [C]
    · exact List.getD_eq_default _ _ (by rw [hClen]; omega)
  have hCle : ∀ x ∈ C, x < 2048 := by
    intro x hx
    simp only [C, List.mem_map, List.mem_range] at hx
    obtain ⟨s, -, rfl⟩ := hx
    calc #{m ∈ range (2 ^ n) | eMask n c m = s} ≤ #(range (2 ^ n)) := card_filter_le _ _
      _ = 2 ^ n := card_range _
      _ < 2048 := h2n
  have hC : ofD C = polyH n c := by
    rw [ofD_eq_sum, hClen, polyH, sumLt_eq]
    have hmaps : ∀ m ∈ range (2 ^ n), eMask n c m ∈ range L := by
      intro m _
      rw [mem_range]
      have := eMask_le n c m
      omega
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl fun s hs => ?_
    rw [hCget, ite_eq_left (mem_range.1 hs), card_eq_sum_ones, sum_mul, one_mul]
    refine sum_congr rfl fun m hm => ?_
    rw [(mem_filter.1 hm).2]
  have hCN : C = N := ofD_inj (hClen.trans hlen.symm) hCle hN (hC.trans h)
  rw [← hCN, hCget]
  split_ifs with hs
  · rfl
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro m _ hm
    have := eMask_le n c m
    omega

/-- **`N_{≤t}` of a coded graph from a certified histogram.** -/
theorem iCount_ofCode_eq {n c : ℕ} (hwf : wfB n c = true) (hn : n ≤ 10) {N : List ℕ}
    (hlen : N.length = n * (n - 1) / 2 + 1) (hN : ∀ x ∈ N, x < 2048) (h : polyH n c = ofD N)
    [DecidableRel (ofCode n c).Adj] (t : ℕ) :
    iCount (ofCode n c) t = ∑ s ∈ range (t + 1), N.getD s 0 := by
  rw [iCount_ofCode hwf, card_eq_sum_card_fiberwise (f := eMask n c) (t := range (t + 1))]
  · refine sum_congr rfl fun s hs => ?_
    rw [← card_eMask_eq hn hlen hN h s, filter_filter]
    congr 1
    refine filter_congr fun m _ => ?_
    constructor
    · exact fun h' => h'.2
    · intro h'
      exact ⟨h' ▸ Nat.lt_succ_iff.1 (mem_range.1 hs), h'⟩
  · intro m hm
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hm
    simp only [coe_range, Set.mem_Iio]
    omega

/-- Degrees of a coded graph. -/
def degB (n c v : ℕ) : ℕ := sumLt n fun w => if adjB n c v w then 1 else 0

theorem card_nbr_ofCode {n c : ℕ} (hwf : wfB n c = true) (v : Fin n) :
    (nbr (ofCode n c) v).card = degB n c v.val := by
  rw [degB, sumLt_eq, ← Fin.sum_univ_eq_sum_range (fun w => if adjB n c v.val w then 1 else 0),
    ← card_filter]
  congr 1
  ext w
  simp [mem_nbr, ofCode_adj hwf]

end P3TS
