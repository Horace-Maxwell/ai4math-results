import Research.Backfill.Paper8.Proof.Rows.Secular

/-!
# Paper 8, rows: members of the two rows exist and satisfy (L) and (Z)

A leaf sum `λ` with `|λ| ≤ n` and `λ ≡ n (mod 2)` is realized by `n` signs (induction on `n`);
this gives the members of the leaf row (Lemma 4.2) and of the bare row (Lemma 4.3). Condition (L)
follows from (P1) and the row conditions, condition (Z) from a branch with at least two leaves
whose leaf sum has absolute value below the number of its leaves ((P2) for the group `b*`).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge

namespace P8Rows

/-- A leaf sum `l` with `|l| ≤ n` and `l ≡ n (mod 2)` is the sum of `n` signs. -/
theorem realize (n : ℕ) (l : ℤ) (h1 : |l| ≤ n) (h2 : Even (l - n)) :
    ∃ g : Fin n → ℝ, (∀ j, g j = 1 ∨ g j = -1) ∧ ∑ j, g j = l := by
  induction n generalizing l with
  | zero =>
    refine ⟨fun j => j.elim0, fun j => j.elim0, ?_⟩
    have : l = 0 := by
      have := abs_nonneg l
      push_cast at h1
      exact abs_eq_zero.1 (le_antisymm h1 this)
    simp [this]
  | succ n ih =>
    by_cases hl : l = (n : ℤ) + 1
    · refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
      simp [hl]
    · have hle : l ≤ (n : ℤ) - 1 := by
        rw [abs_le] at h1
        obtain ⟨c, hc⟩ := h2
        push_cast at h1 hc
        omega
      have h1' : |l + 1| ≤ (n : ℤ) := by
        rw [abs_le] at h1 ⊢
        push_cast at h1
        omega
      have h2' : Even (l + 1 - n) := by
        obtain ⟨c, hc⟩ := h2
        exact ⟨c + 1, by push_cast at hc; omega⟩
      obtain ⟨g, hg1, hg2⟩ := ih (l + 1) h1' h2'
      refine ⟨Fin.cons (-1) g, fun j => ?_, ?_⟩
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp
        · simpa using hg1 j
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hg2]
        push_cast
        ring

variable {k : ℕ} (a : Fin k → ℕ)

theorem lamStd_bare (i : Fin k) (hi : a i = 0) : lamStd a i = 0 := by
  simp [lamStd, hi]

/-- The standard leaf sums are realizable (also on bare branches, where `λ°_i = 0`). -/
theorem lamStd_realizable (hStd : StdLeafSums) (i : Fin k) :
    |lamStd a i| ≤ (a i : ℤ) ∧ Even (lamStd a i - (a i : ℤ)) := by
  rcases Nat.eq_zero_or_pos (a i) with h | h
  · rw [lamStd_bare a i h, h]
    simp
  · exact (hStd k a).1 i h

theorem lam_mkSw (c : ℝ) (mid : Fin k → ℝ) (leafS : (i : Fin k) → Fin (a i) → ℝ) (i : Fin k) :
    lam a (mkSw a c mid leafS) i = ∑ j, leafS i j := rfl

theorem isSwitching_mkSw (c : ℝ) (mid : Fin k → ℝ) (leafS : (i : Fin k) → Fin (a i) → ℝ)
    (hc : c = 1 ∨ c = -1) (hmid : ∀ i, mid i = 1 ∨ mid i = -1)
    (hleaf : ∀ i j, leafS i j = 1 ∨ leafS i j = -1) : IsSwitching (mkSw a c mid leafS) := by
  intro v
  rcases v with _ | ⟨i, _ | j⟩
  · exact hc
  · exact hmid i
  · exact hleaf i j

theorem cast_mem_pm {ε : ℤ} (hε : ε ∈ ({1, -1} : Set ℤ)) : (ε : ℝ) = 1 ∨ (ε : ℝ) = -1 := by
  rcases hε with h | h
  · left; simp [h]
  · right
    rw [Set.mem_singleton_iff] at h
    simp [h]

/-- Members of the leaf row exist (Lemma 4.2, first claim). -/
theorem exists_leafRowMember (hStd : StdLeafSums) (β : ℕ) (ε : ℤ)
    (hε : ε ∈ ({1, -1} : Set ℤ)) (Λ : ℤ) (hΛ : Λ ∈ Lset β (kb (branchMS a) β)) :
    ∃ s, IsLeafRowMember a β ε Λ s := by
  classical
  obtain ⟨l, hl, hsum, hne, hlt⟩ := hΛ
  let e : ↥(Ib a β) ≃ Fin (kb (branchMS a) β) := Finset.equivFinOfCardEq (card_Ib a β)
  let lt : Fin k → ℤ := fun i => if h : i ∈ Ib a β then l (e ⟨i, h⟩) else lamStd a i
  have hlt_mem : ∀ (i : Fin k) (h : i ∈ Ib a β), lt i = l (e ⟨i, h⟩) := fun i h => dite_eq_left h
  have hlt_not : ∀ i, i ∉ Ib a β → lt i = lamStd a i := fun i h => dite_eq_right h
  have hreal : ∀ i, |lt i| ≤ (a i : ℤ) ∧ Even (lt i - (a i : ℤ)) := by
    intro i
    by_cases h : i ∈ Ib a β
    · rw [hlt_mem i h, (mem_Ib a β i).1 h]
      exact hl _
    · rw [hlt_not i h]
      exact lamStd_realizable a hStd i
  choose g hg1 hg2 using fun i => realize (a i) (lt i) (hreal i).1 (hreal i).2
  have hlam : ∀ i, lam a (mkSw a ε (fun _ => 1) g) i = lt i := fun i => hg2 i
  have he : ∀ j, lt (e.symm j) = l j := by
    intro j
    rw [hlt_mem _ (e.symm j).2]
    simp
  refine ⟨mkSw a ε (fun _ => 1) g,
    isSwitching_mkSw a _ _ _ (cast_mem_pm hε) (fun _ => Or.inl rfl) hg1, rfl, fun _ => rfl,
    fun i _ hi => ?_, ?_, fun h2 => ?_, fun h2 => ?_⟩
  · rw [hlam, hlt_not i (fun h => hi ((mem_Ib a β i).1 h))]
  · rw [← hsum]
    push_cast
    rw [← Finset.sum_coe_sort (Ib a β)]
    simp only [hlam]
    rw [← e.sum_comp (fun j => (l j : ℝ))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hlt_mem x.1 x.2]
  · obtain ⟨j, j', hjj'⟩ := hne h2
    refine ⟨e.symm j, (e.symm j).2, e.symm j', (e.symm j').2, ?_⟩
    rw [hlam, hlam, he, he]
    exact_mod_cast hjj'
  · obtain ⟨j, hj⟩ := hlt h2
    refine ⟨e.symm j, (e.symm j).2, ?_⟩
    rw [hlam, he]
    exact_mod_cast hj

/-- Members of the bare row exist (Lemma 4.3, first claim). -/
theorem exists_bareRowMember (hStd : StdLeafSums) (ε : ℤ) (hε : ε ∈ ({1, -1} : Set ℤ))
    (mm : ℕ) (hmm : mm ≤ kb (branchMS a) 0) : ∃ s, IsBareRowMember a ε mm s := by
  classical
  obtain ⟨M, hMsub, hMcard⟩ :=
    Finset.exists_subset_card_eq (s := Ib a 0) (n := mm) (by rw [card_Ib]; exact hmm)
  choose g hg1 hg2 using fun i =>
    realize (a i) (lamStd a i) (lamStd_realizable a hStd i).1 (lamStd_realizable a hStd i).2
  refine ⟨mkSw a ε (fun i => if i ∈ M then -1 else 1) g, ?_, rfl, fun i hi => ⟨?_, hg2 i⟩, ?_⟩
  · refine isSwitching_mkSw a _ _ _ (cast_mem_pm hε) (fun i => ?_) hg1
    by_cases h : i ∈ M
    · right; simp [h]
    · left; simp [h]
  · have : i ∉ M := fun h => by
      have := (mem_Ib a 0 i).1 (hMsub h)
      omega
    show (if i ∈ M then -1 else 1) = (1 : ℝ)
    simp [this]
  · rw [← hMcard]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩
      by_contra hM
      have : (if i ∈ M then -1 else 1 : ℝ) = -1 := h
      rw [ite_eq_right hM] at this
      norm_num at this
    · intro h
      exact ⟨hMsub h, show (if i ∈ M then -1 else 1 : ℝ) = -1 by simp [h]⟩

/-- Leaves of both signs on a branch whose leaf sum is smaller than its number of leaves. -/
theorem exists_leaf_ne (s : TV a → ℝ) (hsw : IsSwitching s) (i : Fin k) (hi : 1 ≤ a i)
    (hlt : |lam a s i| < a i) : ∃ j j', s (some ⟨i, some j⟩) ≠ s (some ⟨i, some j'⟩) := by
  by_contra hcon
  push Not at hcon
  let j0 : Fin (a i) := ⟨0, hi⟩
  have hlam : lam a s i = a i * s (some ⟨i, some j0⟩) := by
    unfold lam
    rw [Finset.sum_congr rfl (fun j _ => hcon j j0), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hlam] at hlt
  rcases hsw (some ⟨i, some j0⟩) with h | h <;> rw [h] at hlt <;> simp at hlt

/-- Condition (Z) from one branch with at least two leaves of both signs. -/
theorem condZ_of_branch (s : TV a → ℝ) (hsw : IsSwitching s) (i : Fin k) (hi : 2 ≤ a i)
    (hlt : |lam a s i| < a i) : condZ a s := by
  obtain ⟨j, j', hjj'⟩ := exists_leaf_ne a s hsw i (by omega) hlt
  exact fun _ => ⟨fun _ => Or.inl ⟨i, hi, j, j', hjj'⟩, fun _ => Or.inl ⟨i, j, j', hjj'⟩⟩

/-- (P2) for the group `b*`: a branch of size `b*` with standard leaf sum below `b*`. -/
theorem exists_std_branch (hStd : StdLeafSums) (hk : 0 < k) (hbs : 2 ≤ bstar (branchMS a)) :
    ∃ i, a i = bstar (branchMS a) ∧ |(lamStd a i : ℝ)| < a i := by
  obtain ⟨i, hi, hpos⟩ := exists_posIn_zero a _ (bstar_mem a hk)
  refine ⟨i, hi, ?_⟩
  have := (hStd k a).2.2 i (by omega) hpos
  exact_mod_cast this

/-- Condition (L) when all `σ_i = 1` on the branches with leaves and the leaf sums in each
group of size `b ≥ 1` with `k_b ≥ 2` are not all equal. -/
theorem condL_of (s : TV a → ℝ) (hsig : ∀ i, 1 ≤ a i → sig a s i = 1)
    (hdist : ∀ b ∈ Bset (branchMS a), 1 ≤ b → 2 ≤ kb (branchMS a) b →
      ∃ i ∈ Ib a b, ∃ i' ∈ Ib a b, lam a s i ≠ lam a s i') : condL a s := by
  intro b hb hb1 hk2 θ hθ
  obtain ⟨i, hi, i', hi', hne⟩ := hdist b hb hb1 hk2
  refine ⟨i, hi, i', hi', ?_⟩
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    have : (b : ℝ) = 0 := by rw [← hθ]; ring
    have : b = 0 := by exact_mod_cast this
    omega
  have hai : a i = b := (mem_Ib a b i).1 hi
  have hai' : a i' = b := (mem_Ib a b i').1 hi'
  rw [hsig i (by omega), hsig i' (by omega)]
  intro h
  apply hne
  have : lam a s i / θ = lam a s i' / θ := by linarith
  rwa [div_left_inj' hθ0] at this

/-- Members of the leaf row satisfy (L) and (Z). -/
theorem leafRow_condL_condZ (hStd : StdLeafSums) (hk : 0 < k) (hbs : 2 ≤ bstar (branchMS a))
    (β : ℕ) (hβ1 : 1 ≤ β) (ε Λ : ℤ) (s : TV a → ℝ) (hs : IsLeafRowMember a β ε Λ s) :
    condL a s ∧ condZ a s := by
  obtain ⟨hsw, -, hsig, hlam, -, hne, hlt⟩ := hs
  refine ⟨condL_of a s (fun i _ => hsig i) (fun b hb hb1 hk2 => ?_), ?_⟩
  · by_cases hbβ : b = β
    · subst hbβ
      exact hne hk2
    · obtain ⟨i, hi, i', hi', hne'⟩ := (hStd k a).2.1 b hb hb1 hk2
      have hai : a i = b := (mem_Ib a b i).1 hi
      have hai' : a i' = b := (mem_Ib a b i').1 hi'
      refine ⟨i, hi, i', hi', ?_⟩
      rw [hlam i (by omega) (by omega), hlam i' (by omega) (by omega)]
      exact_mod_cast hne'
  · by_cases hβ2 : 2 ≤ β
    · obtain ⟨i, hi, hlti⟩ := hlt hβ2
      have hai : a i = β := (mem_Ib a β i).1 hi
      refine condZ_of_branch a s hsw i (by omega) ?_
      rw [hai]
      exact hlti
    · obtain ⟨i, hi, hlti⟩ := exists_std_branch a hStd hk hbs
      refine condZ_of_branch a s hsw i (by omega) ?_
      rw [hlam i (by omega) (by omega)]
      exact hlti

/-- Members of the bare row satisfy (L) and (Z). -/
theorem bareRow_condL_condZ (hStd : StdLeafSums) (hk : 0 < k) (hbs : 2 ≤ bstar (branchMS a))
    (ε : ℤ) (mm : ℕ) (s : TV a → ℝ) (hs : IsBareRowMember a ε mm s) :
    condL a s ∧ condZ a s := by
  obtain ⟨hsw, -, hstd, -⟩ := hs
  refine ⟨condL_of a s (fun i hi => (hstd i hi).1) (fun b hb hb1 hk2 => ?_), ?_⟩
  · obtain ⟨i, hi, i', hi', hne'⟩ := (hStd k a).2.1 b hb hb1 hk2
    have hai : a i = b := (mem_Ib a b i).1 hi
    have hai' : a i' = b := (mem_Ib a b i').1 hi'
    refine ⟨i, hi, i', hi', ?_⟩
    rw [(hstd i (by omega)).2, (hstd i' (by omega)).2]
    exact_mod_cast hne'
  · obtain ⟨i, hi, hlti⟩ := exists_std_branch a hStd hk hbs
    refine condZ_of_branch a s hsw i (by omega) ?_
    rw [(hstd i (by omega)).2]
    exact hlti

end P8Rows
