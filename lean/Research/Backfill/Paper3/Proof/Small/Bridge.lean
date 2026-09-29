import Research.Backfill.Paper3.Challenge
import Research.Backfill.Paper3.Proof.Basic
import Research.Backfill.Paper3.Proof.Small.Defs

/-!
# Small graphs: meaning of the bit-mask checkers

`maskGraph n c` is the graph on `Fin n` with edge mask `c` (see `Research.Backfill.Paper3.Proof.Small.Defs`). The loops
`nall`, `countB`, `sumB` are a conjunction, a count and a sum over `range n`, and `bit` is
`Nat.testBit`. The vertex sets of `Fin n` are the vertex masks `a < 2^n` (`ofMask`), the edges
inside a set are counted over the pairs `i < j`, and so `N_{≤t}(maskGraph n c) = nleB n c t`
(`iCount_maskGraph`). The degree and regularity checkers `degB`, `regB` are proved correct for
every `LocallyFinite` instance.
-/

set_option autoImplicit false

namespace P3Small

open Finset SimpleGraph BackfillPaper3.Challenge

/-! ### Loops -/

theorem nall_iff (n : ℕ) (p : ℕ → Bool) : nall n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero =>
    change true = true ↔ _
    simp
  | succ n ih =>
    change (p n && nall n p) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h2 k hk
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem countB_eq_card (n : ℕ) (p : ℕ → Bool) :
    countB n p = #((range n).filter fun k => p k = true) := by
  induction n with
  | zero =>
    change 0 = _
    simp
  | succ n ih =>
    change cond (p n) (Nat.add (countB n p) 1) (countB n p) = _
    rw [range_add_one, filter_insert]
    cases h : p n
    · simpa using ih
    · have hn : n ∉ (range n).filter fun k => p k = true := by simp
      rw [ite_eq_left rfl, card_insert_of_notMem hn]
      exact congrArg (· + 1) ih

theorem sumB_eq_sum (n : ℕ) (g : ℕ → ℕ) : sumB n g = ∑ k ∈ range n, g k := by
  induction n with
  | zero =>
    change 0 = _
    simp
  | succ n ih =>
    change Nat.add (g n) (sumB n g) = _
    rw [sum_range_succ, ih, Nat.add_eq, add_comm]

/-! ### Bits and pair indices -/

theorem bit_eq_testBit (m i : ℕ) : bit m i = m.testBit i := by
  rw [Bool.eq_iff_iff, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  show Nat.beq ((m >>> i) &&& 1) 1 = true ↔ _
  rw [Nat.beq_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem blt_true {i j : ℕ} (h : i < j) : Nat.blt i j = true := by
  rw [Nat.blt_eq]
  exact h

theorem blt_false {i j : ℕ} (h : ¬ i < j) : Nat.blt i j = false := by
  cases hb : Nat.blt i j
  · rfl
  · rw [Nat.blt_eq] at hb
    exact absurd hb h

theorem beq_false {i j : ℕ} (h : i ≠ j) : Nat.beq i j = false := by
  cases hb : Nat.beq i j
  · rfl
  · rw [Nat.beq_eq] at hb
    exact absurd hb h

theorem pidx_comm (i j : ℕ) : pidx i j = pidx j i := by
  unfold pidx
  rcases lt_trichotomy i j with h | rfl | h
  · rw [blt_true h, blt_false (show ¬ j < i by omega)]
    rfl
  · rfl
  · rw [blt_false (show ¬ i < j by omega), blt_true h]
    rfl

theorem adjB_comm (c i j : ℕ) : adjB c i j = adjB c j i := by
  unfold adjB
  rw [pidx_comm i j]
  by_cases h : i = j
  · subst h
    rfl
  · rw [beq_false h, beq_false (Ne.symm h)]

theorem adjB_self (c i : ℕ) : adjB c i i = false := by
  unfold adjB
  rw [Nat.beq_refl]
  rfl

theorem adjB_of_ne (c : ℕ) {i j : ℕ} (h : i ≠ j) : adjB c i j = bit c (pidx i j) := by
  unfold adjB
  rw [beq_false h]
  rfl

/-! ### The graph of an edge mask -/

/-- The graph on `Fin n` with edge mask `c`. -/
def maskGraph (n c : ℕ) : SimpleGraph (Fin n) where
  Adj i j := adjB c i.val j.val = true
  symm := ⟨fun i j h => by rw [adjB_comm]; exact h⟩
  loopless := ⟨fun i h => by rw [adjB_self] at h; exact Bool.false_ne_true h⟩

instance (n c : ℕ) : DecidableRel (maskGraph n c).Adj := fun i j =>
  inferInstanceAs (Decidable (adjB c i.val j.val = true))

theorem maskGraph_adj {n c : ℕ} {i j : Fin n} :
    (maskGraph n c).Adj i j ↔ adjB c i.val j.val = true := Iff.rfl

/-! ### Edges inside a vertex set, counted over pairs `i < j` -/

/-- `e_G(A)` is the number of pairs `i < j` of adjacent vertices of `A`. -/
theorem edgesIn_eq_card_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) :
    edgesIn G A = #(univ.filter fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A) := by
  have h := P3Basic.two_mul_edgesIn G A
  have hsplit : #(univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A) =
      #(univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A) +
      #(univ.filter fun p : Fin n × Fin n => p.2 < p.1 ∧ G.Adj p.1 p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A) := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext p
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨hadj, h1, h2⟩
        rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hlt
        · exact Or.inl ⟨hlt, hadj, h1, h2⟩
        · exact Or.inr ⟨hlt, hadj, h1, h2⟩
      · rintro (⟨_, hadj, h1, h2⟩ | ⟨_, hadj, h1, h2⟩) <;> exact ⟨hadj, h1, h2⟩
    · rw [disjoint_filter]
      rintro p _ ⟨h1, _⟩ ⟨h2, _⟩
      exact lt_asymm h1 h2
  have hswap :
      #(univ.filter fun p : Fin n × Fin n => p.2 < p.1 ∧ G.Adj p.1 p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A) =
      #(univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A) := by
    apply card_bij (fun p _ => p.swap)
    · rintro ⟨a, b⟩ hp
      simp only [mem_filter, mem_univ, true_and, Prod.swap_prod_mk] at hp ⊢
      exact ⟨hp.1, hp.2.1.symm, hp.2.2.2, hp.2.2.1⟩
    · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at h
      rw [h.1, h.2]
    · rintro ⟨a, b⟩ hp
      refine ⟨(b, a), ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      exact ⟨hp.1, hp.2.1.symm, hp.2.2.2, hp.2.2.1⟩
  omega

/-- Counting pairs of `Fin n` by a double sum over `range n`. -/
theorem card_filter_pairs (n : ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P] :
    #(univ.filter fun p : Fin n × Fin n => P p.1 p.2) =
      ∑ j ∈ range n, ∑ i ∈ range n, if P i j then 1 else 0 := by
  calc #(univ.filter fun p : Fin n × Fin n => P p.1 p.2)
      = ∑ p : Fin n × Fin n, if P p.1 p.2 then 1 else 0 := by rw [card_filter]
    _ = ∑ i : Fin n, ∑ j : Fin n, if P i j then 1 else 0 := Fintype.sum_prod_type _
    _ = ∑ j : Fin n, ∑ i : Fin n, if P i j then 1 else 0 := Finset.sum_comm
    _ = ∑ j : Fin n, ∑ i ∈ range n, if P i j then 1 else 0 :=
        sum_congr rfl fun j _ => Fin.sum_univ_eq_sum_range (fun i => if P i j then 1 else 0) n
    _ = ∑ j ∈ range n, ∑ i ∈ range n, if P i j then 1 else 0 :=
        Fin.sum_univ_eq_sum_range (fun j => ∑ i ∈ range n, if P i j then 1 else 0) n

theorem pairsIn_eq_sum (n c a : ℕ) : pairsIn n c a =
    ∑ j ∈ range n, ∑ i ∈ range n,
      if i < j ∧ bit c (pidx i j) = true ∧ bit a i = true ∧ bit a j = true then 1 else 0 := by
  unfold pairsIn
  rw [sumB_eq_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  cases hb : bit a j
  · simp
  · change sumB j _ = _
    rw [sumB_eq_sum, ← sum_range_add_sum_Ico _ hj.le, sum_eq_zero (s := Ico j n), add_zero]
    · refine sum_congr rfl fun i hi => ?_
      rw [mem_range] at hi
      cases h1 : bit a i <;> cases h2 : bit c (pidx i j) <;> simp [hi]
    · intro i hi
      rw [mem_Ico] at hi
      simp [not_lt.mpr hi.1]

/-- The vertex set of `Fin n` with vertex mask `a`. -/
def ofMask (n a : ℕ) : Finset (Fin n) := univ.filter fun i => bit a i.val = true

theorem mem_ofMask {n a : ℕ} {i : Fin n} : i ∈ ofMask n a ↔ bit a i.val = true := by
  simp [ofMask]

theorem edgesIn_maskGraph (n c a : ℕ) :
    edgesIn (maskGraph n c) (ofMask n a) = pairsIn n c a := by
  rw [edgesIn_eq_card_lt, pairsIn_eq_sum, ← card_filter_pairs n
    (fun i j => i < j ∧ bit c (pidx i j) = true ∧ bit a i = true ∧ bit a j = true)]
  congr 1
  refine filter_congr fun p _ => ?_
  rw [maskGraph_adj, mem_ofMask, mem_ofMask, Fin.lt_def]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by rwa [adjB_of_ne c (Nat.ne_of_lt h1)] at h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by rwa [adjB_of_ne c (Nat.ne_of_lt h1)], h3, h4⟩

/-! ### Vertex sets as vertex masks -/

theorem ofMask_injOn (n : ℕ) : Set.InjOn (ofMask n) (range (2 ^ n) : Set ℕ) := by
  intro a ha b hb hab
  have ha' : a < 2 ^ n := by simpa using ha
  have hb' : b < 2 ^ n := by simpa using hb
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · have h1 : (⟨k, hk⟩ : Fin n) ∈ ofMask n a ↔ (⟨k, hk⟩ : Fin n) ∈ ofMask n b := by rw [hab]
    rw [mem_ofMask, mem_ofMask, bit_eq_testBit, bit_eq_testBit] at h1
    exact Bool.eq_iff_iff.mpr h1
  · have h2 : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha' h2),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb' h2)]

/-- Counting vertex sets of `Fin n` by their vertex masks. -/
theorem card_filter_finset_fin (n : ℕ) (P : Finset (Fin n) → Prop) [DecidablePred P] :
    #(univ.filter P) = #((range (2 ^ n)).filter fun a => P (ofMask n a)) := by
  have himg : (range (2 ^ n)).image (ofMask n) = univ := by
    apply eq_univ_of_card
    rw [card_image_of_injOn (ofMask_injOn n), card_range, Fintype.card_finset, Fintype.card_fin]
  rw [← himg, filter_image, card_image_of_injOn]
  exact (ofMask_injOn n).mono (coe_subset.mpr (filter_subset _ _))

/-- `N_{≤t}` of the graph with edge mask `c` is computed by `nleB`. -/
theorem iCount_maskGraph (n c t : ℕ) : iCount (maskGraph n c) t = nleB n c t := by
  unfold iCount nleB
  rw [card_filter_finset_fin, countB_eq_card, Nat.pow_eq]
  congr 1
  refine filter_congr fun a _ => ?_
  rw [edgesIn_maskGraph, Nat.ble_eq]

/-! ### Degrees and regularity -/

theorem card_filter_fin (n : ℕ) (q : ℕ → Bool) :
    #(univ.filter fun j : Fin n => q j.val = true) = #((range n).filter fun k => q k = true) := by
  rw [card_filter, card_filter]
  exact Fin.sum_univ_eq_sum_range (fun k => if q k = true then 1 else 0) n

theorem degree_maskGraph' (n c : ℕ) (i : Fin n) : (maskGraph n c).degree i = degB n c i := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, degB, countB_eq_card]
  exact card_filter_fin n (adjB c i.val)

/-- The degree checker, for any `Fintype` instance on the neighbour set. -/
theorem degree_maskGraph (n c : ℕ) (i : Fin n) {inst : Fintype ((maskGraph n c).neighborSet i)} :
    @degree _ (maskGraph n c) i inst = degB n c i := by
  convert degree_maskGraph' n c i

/-- The regularity checker, for any `LocallyFinite` instance. -/
theorem isRegular_maskGraph_iff (n c d : ℕ) {inst : (maskGraph n c).LocallyFinite} :
    @IsRegularOfDegree _ (maskGraph n c) inst d ↔ regB n c d = true := by
  rw [regB, nall_iff]
  constructor
  · intro h k hk
    have h1 := h ⟨k, hk⟩
    rw [degree_maskGraph] at h1
    rw [Nat.beq_eq]
    exact h1
  · intro h v
    have h1 := h v.val v.isLt
    rw [Nat.beq_eq] at h1
    rw [degree_maskGraph]
    exact h1

/-- Regularity is invariant under isomorphism (for any `LocallyFinite` instances). -/
theorem regular_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {instG : G.LocallyFinite} {instH : H.LocallyFinite} (f : G ≃g H) {d : ℕ}
    (h : @IsRegularOfDegree _ G instG d) : @IsRegularOfDegree _ H instH d := by
  intro w
  have h1 := f.degree_eq (f.symm w)
  rw [RelIso.apply_symm_apply] at h1
  rw [h1]
  exact h (f.symm w)

end P3Small
