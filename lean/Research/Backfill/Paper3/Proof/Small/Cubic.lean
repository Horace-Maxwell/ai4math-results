import Research.Backfill.Paper3.Proof.Small.Bridge
import Research.Backfill.Paper3.Proof.Small.Enum

/-!
# Cubic graphs on six vertices (`CubicSix`)

Every graph on `Fin 6` is `maskGraph 6 c` for exactly one edge mask `c < 2^15` (`exists_mask6`,
`maskGraph6_inj`; also used for `LabelledCounts` in `Research.Backfill.Paper3.Proof.Small.Labelled`). By the kernel
enumeration of `Research.Backfill.Paper3.Proof.Small.Enum`, every cubic mask has a checked permutation onto the mask of
`K_{3,3}` or of the prism. A cubic graph on an arbitrary six-element type is transported to
`Fin 6` by `Fintype.equivFinOfCardEq`.
-/

set_option autoImplicit false

namespace P3Small

open Finset SimpleGraph BackfillPaper3.Challenge

/-! ### Edge masks of the graphs on `Fin 6` -/

/-- The first vertex of the pair with index `k < 15`. -/
def pfst (k : ℕ) : Fin 6 :=
  ⟨[0, 0, 1, 0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3, 4].getD k 0 % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The second vertex of the pair with index `k < 15`. -/
def psnd (k : ℕ) : Fin 6 :=
  ⟨[1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5].getD k 0 % 6, Nat.mod_lt _ (by norm_num)⟩

theorem pidx_spec : ∀ i j : Fin 6, i ≠ j → pidx i.val j.val < 15 ∧
    ((pfst (pidx i.val j.val) = i ∧ psnd (pidx i.val j.val) = j) ∨
      (pfst (pidx i.val j.val) = j ∧ psnd (pidx i.val j.val) = i)) := by
  decide +kernel

theorem pdec_spec : ∀ k < 15, pfst k ≠ psnd k ∧ pidx (pfst k).val (psnd k).val = k := by
  decide +kernel

/-- Prescribed low bits. -/
theorem exists_testBit (N : ℕ) (f : ℕ → Bool) : ∃ c < 2 ^ N, ∀ k < N, c.testBit k = f k := by
  induction N with
  | zero => exact ⟨0, by norm_num, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ N ih =>
    obtain ⟨c, hc, hf⟩ := ih
    cases hN : f N
    · refine ⟨c, lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N)),
        fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact hf k hk
      · rw [hk, Nat.testBit_lt_two_pow hc, hN]
    · refine ⟨2 ^ N + c, by rw [pow_succ]; omega, fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · rw [Nat.testBit_two_pow_add_gt hk, hf k hk]
      · rw [hk]
        simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hc, hN]

/-- Every graph on `Fin 6` has an edge mask `c < 2^15`. -/
theorem exists_mask6 (G : SimpleGraph (Fin 6)) :
    ∃ c < 2 ^ 15, ∀ i j, G.Adj i j ↔ (maskGraph 6 c).Adj i j := by
  classical
  obtain ⟨c, hc, hf⟩ := exists_testBit 15 (fun k => decide (G.Adj (pfst k) (psnd k)))
  have hf' : ∀ k < 15, c.testBit k = decide (G.Adj (pfst k) (psnd k)) := hf
  refine ⟨c, hc, fun i j => ?_⟩
  rw [maskGraph_adj]
  by_cases hij : i = j
  · subst hij
    rw [adjB_self]
    simp
  · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    obtain ⟨hlt, hdec⟩ := pidx_spec i j hij
    rw [adjB_of_ne c hne, bit_eq_testBit, hf' _ hlt, decide_eq_true_iff]
    rcases hdec with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]
      exact G.adj_comm i j

/-- Edge masks below `2^15` are determined by their graphs. -/
theorem maskGraph6_inj {c c' : ℕ} (hc : c < 2 ^ 15) (hc' : c' < 2 ^ 15)
    (h : maskGraph 6 c = maskGraph 6 c') : c = c' := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 15
  · obtain ⟨hne, hk'⟩ := pdec_spec k hk
    have hne' : (pfst k).val ≠ (psnd k).val := fun h => hne (Fin.ext h)
    have h1 : (maskGraph 6 c).Adj (pfst k) (psnd k) ↔ (maskGraph 6 c').Adj (pfst k) (psnd k) := by
      rw [h]
    rw [maskGraph_adj, maskGraph_adj, adjB_of_ne _ hne', adjB_of_ne _ hne', hk', bit_eq_testBit,
      bit_eq_testBit] at h1
    exact Bool.eq_iff_iff.mpr h1
  · have h2 : 2 ^ 15 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc h2),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc' h2)]

/-! ### Isomorphism certificates -/

/-- The map of `Fin 6` with permutation code `π`. -/
def permFun (π : ℕ) (i : Fin 6) : Fin 6 := ⟨pimg π i.val % 6, Nat.mod_lt _ (by norm_num)⟩

/-- A checked certificate gives an isomorphism. -/
theorem iso_of_cert {c c' π : ℕ} (hπ : permOK π = true) (h : isoOK c c' π = true) :
    Nonempty (maskGraph 6 c ≃g maskGraph 6 c') := by
  unfold permOK at hπ
  rw [Bool.and_eq_true, nall_iff, nall_iff] at hπ
  obtain ⟨hlt, hinj⟩ := hπ
  have hval : ∀ i : Fin 6, (permFun π i).val = pimg π i.val := fun i => by
    have h1 := hlt i.val i.isLt
    rw [Nat.blt_eq] at h1
    exact Nat.mod_eq_of_lt h1
  have hinj' : Function.Injective (permFun π) := by
    intro i j hij
    by_contra hne
    have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have h1 := hinj i.val i.isLt
    rw [nall_iff] at h1
    have h2 := h1 j.val j.isLt
    have h3 : pimg π i.val = pimg π j.val := by rw [← hval, ← hval, hij]
    rw [beq_false hne', h3, Nat.beq_refl] at h2
    exact absurd h2 (by decide)
  refine ⟨⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj'), fun {a b} => ?_⟩⟩
  unfold isoOK at h
  rw [nall_iff] at h
  have h1 := h a.val a.isLt
  rw [nall_iff] at h1
  have h2 := h1 b.val b.isLt
  show adjB c' (permFun π a).val (permFun π b).val = true ↔ adjB c a.val b.val = true
  rw [hval, hval]
  revert h2
  unfold beqB
  cases adjB c a.val b.val <;> cases adjB c' (pimg π a.val) (pimg π b.val) <;> simp

theorem certOK_of_regB {c : ℕ} (hc : c < 2 ^ 15) (hreg : regB 6 c 3 = true) :
    certOK c = true := by
  have h := allCert_eq
  unfold allCert at h
  rw [nall_iff] at h
  have h1 := h c (lt_of_lt_of_eq hc (by norm_num))
  rw [hreg] at h1
  simpa using h1

theorem cubic_mask6 {c : ℕ} (hc : c < 2 ^ 15) (hreg : regB 6 c 3 = true) :
    Nonempty (maskGraph 6 c ≃g maskGraph 6 k33Mask) ∨
      Nonempty (maskGraph 6 c ≃g maskGraph 6 prismMask) := by
  have h := certOK_of_regB hc hreg
  unfold certOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases hb : (findCert c certs6).2
  · rw [hb] at h2
    exact Or.inl (iso_of_cert h1 h2)
  · rw [hb] at h2
    exact Or.inr (iso_of_cert h1 h2)

/-- `K_{3,3}` is the mask graph `k33Mask` (`inl i ↦ i`, `inr j ↦ 3 + j`). -/
def isoK33 : Kdd 3 ≃g maskGraph 6 k33Mask where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by decide +kernel

/-- The prism is the mask graph `prismMask` (`(a, b) ↦ 2a + b`). -/
def isoPrism : prism ≃g maskGraph 6 prismMask where
  toEquiv := finProdFinEquiv
  map_rel_iff' := by decide +kernel

/-- The prism is cubic (for any `LocallyFinite` instance). -/
theorem prism_regular {inst : prism.LocallyFinite} : @IsRegularOfDegree _ prism inst 3 := by
  have h : (maskGraph 6 prismMask).IsRegularOfDegree 3 :=
    (isRegular_maskGraph_iff 6 prismMask 3).mpr regB_prism
  exact regular_of_iso isoPrism.symm h

/-! ### The two statements -/

/-- §1: every cubic graph on six vertices is `K_{3,3}` or the prism. -/
theorem cubicSix : CubicSix := by
  intro V _ _ G _ hV hG
  let e : V ≃ Fin 6 := Fintype.equivFinOfCardEq hV
  obtain ⟨c, hc, hadj⟩ := exists_mask6 (G.comap e.symm)
  let f : G ≃g maskGraph 6 c :=
    (Iso.comap e.symm G).symm.trans ⟨Equiv.refl _, fun {a b} => (hadj a b).symm⟩
  have hreg : (maskGraph 6 c).IsRegularOfDegree 3 := regular_of_iso f hG
  rw [isRegular_maskGraph_iff] at hreg
  rcases cubic_mask6 hc hreg with h | h
  · obtain ⟨g⟩ := h
    exact Or.inl ⟨f.trans (g.trans isoK33.symm)⟩
  · obtain ⟨g⟩ := h
    exact Or.inr ⟨f.trans (g.trans isoPrism.symm)⟩

end P3Small
