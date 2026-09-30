import Research.Backfill.Paper8.Proof.Tree.Transfer
import Research.Backfill.Paper8.Proof.Main.Main
import Research.Backfill.Paper8.Proof.Small.Main

/-!
# Paper 8, Theorem 1

A tree `T` of diameter at most `4` other than `K_2`: `K_1` is handled directly; otherwise
`T ≅ T(a)` (`treeStructure_fwd`) and a good switching of `T(a)` is transferred along the
isomorphism. For `T(a)`: `b* ≤ 1` by Proposition 5.1; `b* ≥ 2` by Corollary 4.4 when (a′) or (b′)
holds (for `b* ≥ 13`, (a′) holds by Proposition 5.3); otherwise `2 ≤ b* ≤ 12`, `a ∈ ℛ`
(Lemma 5.4) and `a` is `(2,2)`, `(2,0,0)` or `(3)` (Proposition 5.5), settled by Proposition 5.6
after relabelling the branches. Lemma 2.1 turns "good" into "every eigenvalue main".
`Theorem1_mathlib` follows by unfolding. Propositions 5.1 and 5.6 are taken from the modules of
agents `small` and `main` in `theorem1`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge SimpleGraph Matrix

namespace P8Tree

section Branches

variable {k : ℕ} (a : Fin k → ℕ)

theorem mem_branchMS (i : Fin k) : a i ∈ branchMS a :=
  Multiset.mem_map_of_mem a (Finset.mem_univ_val i)

theorem card_branchMS : Multiset.card (branchMS a) = k := by
  simp [branchMS]

theorem sum_branchMS : (branchMS a).sum = ∑ i, a i := rfl

theorem le_bstar (i : Fin k) : a i ≤ bstar (branchMS a) :=
  Finset.le_sup (f := id) (Multiset.mem_toFinset.2 (mem_branchMS a i))

theorem exists_of_kb_pos {b : ℕ} (h : 1 ≤ kb (branchMS a) b) : ∃ i, a i = b := by
  have hb : b ∈ branchMS a := Multiset.count_pos.1 (by unfold kb at h; omega)
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hb
  exact ⟨i, hi⟩

theorem ne_of_kb_zero {b : ℕ} (h : kb (branchMS a) b = 0) (i : Fin k) : a i ≠ b := by
  intro hi
  have hb : b ∈ branchMS a := hi ▸ mem_branchMS a i
  have := Multiset.count_pos.2 hb
  unfold kb at h
  omega

theorem kb_le (b : ℕ) : kb (branchMS a) b ≤ k := by
  unfold kb
  calc Multiset.count b (branchMS a) ≤ Multiset.card (branchMS a) := Multiset.count_le_card _ _
    _ = k := card_branchMS a

end Branches

section Switchings

theorem isSwitching_mkSw {k : ℕ} (a : Fin k → ℕ) {c : ℝ} {mid : Fin k → ℝ}
    {leafS : (i : Fin k) → Fin (a i) → ℝ} (hc : c = 1 ∨ c = -1)
    (hm : ∀ i, mid i = 1 ∨ mid i = -1) (hl : ∀ i j, leafS i j = 1 ∨ leafS i j = -1) :
    IsSwitching (mkSw a c mid leafS) := by
  intro v
  rcases v with _ | ⟨i, _ | j⟩
  · exact hc
  · exact hm i
  · exact hl i j

theorem ite_neg_one (p : Prop) [Decidable p] :
    (if p then (-1 : ℝ) else 1) = 1 ∨ (if p then (-1 : ℝ) else 1) = -1 := by
  split_ifs <;> simp

theorem ite_one (p : Prop) [Decidable p] :
    (if p then (1 : ℝ) else -1) = 1 ∨ (if p then (1 : ℝ) else -1) = -1 := by
  split_ifs <;> simp

theorem lamStd_pm {k : ℕ} (a : Fin k → ℕ) (i : Fin k) (h : a i = 1) :
    (lamStd a i : ℝ) = 1 ∨ (lamStd a i : ℝ) = -1 := by
  have h' : lamStd a i = 1 ∨ lamStd a i = -1 := by
    unfold lamStd
    split_ifs <;> omega
  rcases h' with h' | h' <;> simp [h']

theorem isSwitching_sw56a : IsSwitching sw56a := by
  refine isSwitching_mkSw _ ?_ ?_ ?_
  · exact Or.inl rfl
  · intro i
    exact Or.inl rfl
  · intro i j
    exact ite_one _

theorem isSwitching_sw56b : IsSwitching sw56b := by
  refine isSwitching_mkSw _ ?_ ?_ ?_
  · exact Or.inl rfl
  · intro i
    exact ite_neg_one _
  · intro i j
    exact ite_one _

theorem isSwitching_sw56c : IsSwitching sw56c := by
  refine isSwitching_mkSw _ ?_ ?_ ?_
  · exact Or.inl rfl
  · intro i
    exact Or.inl rfl
  · intro i j
    exact ite_one _

end Switchings

/-- The case `b* ≤ 1` (Proposition 5.1). -/
theorem good_small (h51 : Prop_5_1) {k : ℕ} (a : Fin k → ℕ) (hk : 0 < k) (hle : ∀ i, a i ≤ 1)
    (hn : 3 ≤ 1 + k + ∑ i, a i) : ∃ s : TV a → ℝ, IsSwitching s ∧ IsGood (adjT a) s := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := h51 k a hk hle hn
  have hleaf : ∀ i, Fin (a i) → a i = 1 := fun i j => by
    have := j.isLt
    have := hle i
    omega
  have hk0 := kb_le a 0
  by_cases h1 : kb (branchMS a) 1 = 0
  · obtain ⟨U, -, hU⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin k)))
      (n := if kb (branchMS a) 0 = 4 then 2 else 1) (by
        rw [Finset.card_univ, Fintype.card_fin]
        split_ifs <;> omega)
    refine ⟨_, ?_, hA h1 U hU⟩
    refine isSwitching_mkSw _ (Or.inl rfl) (fun i => ?_) (fun _ _ => Or.inl rfl)
    exact ite_neg_one _
  · by_cases h02 : 2 ≤ kb (branchMS a) 0
    · obtain ⟨i0, hi0⟩ := exists_of_kb_pos a (b := 0) (by omega)
      by_cases h11 : kb (branchMS a) 1 = 1
      · refine ⟨_, ?_, hB h11 h02 i0 hi0⟩
        refine isSwitching_mkSw _ (Or.inl rfl) (fun i => ?_) (fun _ _ => Or.inr rfl)
        exact ite_neg_one _
      · obtain ⟨i1, hi1⟩ := exists_of_kb_pos a (b := 1) (by omega)
        refine ⟨_, ?_, hC (by omega) h02 i0 i1 hi0 hi1⟩
        refine isSwitching_mkSw _ (Or.inl rfl) (fun i => ?_) (fun i _ => ?_)
        · exact ite_neg_one _
        · exact ite_neg_one _
    · by_cases h00 : kb (branchMS a) 0 = 0
      · refine ⟨_, ?_, hE h00⟩
        exact isSwitching_mkSw _ (Or.inl rfl) (fun _ => Or.inl rfl)
          (fun i j => lamStd_pm a i (hleaf i j))
      · obtain ⟨ε, hε, hg⟩ := hD (by omega)
        refine ⟨_, ?_, hg⟩
        refine isSwitching_mkSw _ ?_ (fun _ => Or.inl rfl) (fun i j => lamStd_pm a i (hleaf i j))
        simpa using hε

/-- The trees `T(2,2)`, `T(2,0,0)` (up to the order of the branches) and `T(3)`
(Proposition 5.6). -/
theorem good_exceptional (h56 : Prop_5_6) {k : ℕ} (a : Fin k → ℕ)
    (hex : branchMS a = {2, 2} ∨ branchMS a = {2, 0, 0} ∨ branchMS a = {3}) :
    ∃ s : TV a → ℝ, IsSwitching s ∧ IsGood (adjT a) s := by
  obtain ⟨⟨hA, -⟩, ⟨hB, -⟩, ⟨hC, -⟩⟩ := h56
  rcases hex with h | h | h
  · have hk : k = 2 := by
      have := card_branchMS a
      rw [h] at this
      simpa using this.symm
    subst hk
    have hv : ∀ i, a i = 2 := by
      intro i
      have := mem_branchMS a i
      rw [h] at this
      simpa using this
    have ha : a = ![2, 2] := by
      funext i
      fin_cases i <;> simp [hv]
    subst ha
    exact ⟨sw56a, isSwitching_sw56a, hA⟩
  · have hk : k = 3 := by
      have := card_branchMS a
      rw [h] at this
      simpa using this.symm
    subst hk
    have hv : ∀ i, a i = 2 ∨ a i = 0 := by
      intro i
      have := mem_branchMS a i
      rw [h] at this
      simpa using this
    have hs : a 0 + a 1 + a 2 = 2 := by
      have := sum_branchMS a
      rw [h, Fin.sum_univ_three] at this
      simpa using this.symm
    rcases hv 0 with h0 | h0 <;> rcases hv 1 with h1 | h1 <;> rcases hv 2 with h2 | h2 <;>
      try omega
    · have ha : a = ![2, 0, 0] := by
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      subst ha
      exact ⟨sw56b, isSwitching_sw56b, hB⟩
    · have ha : a = ![0, 2, 0] := by
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      subst ha
      let ψ := permIso (a := ![0, 2, 0]) (a' := ![2, 0, 0]) (Equiv.swap 0 1) (by decide)
      exact ⟨sw56b ∘ ψ, isSwitching_comp isSwitching_sw56b, isGood_of_iso ψ hB⟩
    · have ha : a = ![0, 0, 2] := by
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      subst ha
      let ψ := permIso (a := ![0, 0, 2]) (a' := ![2, 0, 0]) (Equiv.swap 0 2) (by decide)
      exact ⟨sw56b ∘ ψ, isSwitching_comp isSwitching_sw56b, isGood_of_iso ψ hB⟩
  · have hk : k = 1 := by
      have := card_branchMS a
      rw [h] at this
      simpa using this.symm
    subst hk
    have ha : a = ![3] := by
      funext i
      fin_cases i
      have := mem_branchMS a 0
      rw [h] at this
      simpa using this
    subst ha
    exact ⟨sw56c, isSwitching_sw56c, hC⟩

/-- The case `b* ≥ 2` (Corollary 4.4, Proposition 5.3, Lemma 5.4, Propositions 5.5, 5.6). -/
theorem good_of_two_le_bstar (h53 : Prop_5_3) (h44 : Cor_4_4) (h54 : Lemma_5_4)
    (h55 : Prop_5_5) (h56 : Prop_5_6) {k : ℕ} (a : Fin k → ℕ) (hk : 0 < k)
    (h2 : 2 ≤ bstar (branchMS a)) : ∃ s : TV a → ℝ, IsSwitching s ∧ IsGood (adjT a) s := by
  by_cases hc : CritA (branchMS a) ∨ CritB (branchMS a)
  · exact (h44 k a hk h2).2.2 hc
  · have h12 : bstar (branchMS a) ≤ 12 := by
      by_contra h13
      push Not at h13
      obtain ⟨hmem, hcrit, -⟩ := h53 k a hk (by omega)
      exact hc (Or.inl ⟨_, hmem, by omega, hcrit⟩)
    have hA : ¬ CritA (branchMS a) := fun h => hc (Or.inl h)
    have hB : ¬ CritB (branchMS a) := fun h => hc (Or.inr h)
    have hreg : branchMS a ∈ regionR := h54.1 k a hk h2 h12 hA hB
    have hex : branchMS a = {2, 2} ∨ branchMS a = {2, 0, 0} ∨ branchMS a = {3} := by
      by_contra hne
      push Not at hne
      exact hc (h55 _ hreg hne.1 hne.2.1 hne.2.2)
    exact good_exceptional h56 a hex

/-- Every `T(a)` with `k ≥ 1` and `n ≥ 3` has a good switching. -/
theorem good_treeT (h51 : Prop_5_1) (h53 : Prop_5_3) (h44 : Cor_4_4) (h54 : Lemma_5_4)
    (h55 : Prop_5_5) (h56 : Prop_5_6) {k : ℕ} (a : Fin k → ℕ) (hk : 0 < k)
    (hn : 3 ≤ 1 + k + ∑ i, a i) : ∃ s : TV a → ℝ, IsSwitching s ∧ IsGood (adjT a) s := by
  by_cases hb : bstar (branchMS a) ≤ 1
  · exact good_small h51 a hk (fun i => le_trans (le_bstar a i) hb) hn
  · exact good_of_two_le_bstar h53 h44 h54 h55 h56 a hk (by omega)

/-- Theorem 1, from the listed statements. -/
theorem theorem1_of (h21 : Lemma_2_1_good) (h51 : Prop_5_1) (h53 : Prop_5_3) (h44 : Cor_4_4)
    (h54 : Lemma_5_4) (h55 : Prop_5_5) (h56 : Prop_5_6) : Theorem1 := by
  intro V _ _ T _ hT hd hK2
  suffices h : ∃ s : V → ℝ, IsSwitching s ∧ IsGood (T.adjMatrix ℝ) s by
    obtain ⟨s, hs, hg⟩ := h
    exact ⟨s, hs, (h21 V (T.adjMatrix ℝ) T.isSymm_adjMatrix s hs).1 hg⟩
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 hT.connected.nonempty
  rcases Nat.lt_or_ge (Fintype.card V) 3 with hlt | h3
  · obtain h1 | h2 : Fintype.card V = 1 ∨ Fintype.card V = 2 := by omega
    · exact ⟨fun _ => 1, fun _ => Or.inl rfl, isGood_one_of_card_one _ h1⟩
    · exact (hK2.false (iso_top_of_card_two T hT h2).some).elim
  · obtain ⟨k, a, hk, ⟨φ⟩⟩ := treeStructure_fwd V T hT hd h3
    have hn : 3 ≤ 1 + k + ∑ i, a i := by
      rw [← P8Basic.card_TV, ← Fintype.card_congr φ.toEquiv]
      exact h3
    obtain ⟨s, hs, hg⟩ := good_treeT h51 h53 h44 h54 h55 h56 a hk hn
    exact ⟨s ∘ φ, isSwitching_comp hs, isGood_of_iso φ hg⟩

/-- Theorem 1, with Proposition 5.6 (`P8Main.check_Prop_5_6`) and Proposition 5.1
(`P8Small.check_Prop_5_1` with `P8Main.check_Lemma_3_2`) from agents `main` and `small`. -/
theorem theorem1 (h21 : Lemma_2_1_good) (h53 : Prop_5_3) (h44 : Cor_4_4) (h54 : Lemma_5_4)
    (h55 : Prop_5_5) : Theorem1 :=
  theorem1_of h21 (P8Small.check_Prop_5_1 P8Main.check_Lemma_3_2) h53 h44 h54 h55
    P8Main.check_Prop_5_6

/-- `Theorem1_mathlib` from `Theorem1` (unfolding the definitions of the challenge file). -/
theorem theorem1_mathlib_of (h : Theorem1) : Theorem1_mathlib := by
  intro V _ _ T _ hT hd hK2
  obtain ⟨s, hs, hmain⟩ := h V T hT hd hK2
  exact ⟨s, hs, fun θ hθ => (hmain θ hθ).2⟩

end P8Tree
