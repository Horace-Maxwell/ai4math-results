import Research.Backfill.Paper7.ZeroDirichletSequence
import Research.Backfill.Paper7.GapKernelDecomposition

/-! Exact original zero-gap dimensions. The even case constructs a genuine
zero-system kernel vector, and the odd case proves every image vector zero. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Lemma22Gaps
open BackfillPaper7.Challenge

def gapIndex (b : ℕ) (K : Finset (Fin b)) (k : Fin b) (hk : k ∈ K)
    (j : {j : Fin b // inGap b K k j}) : ℕ :=
  Classical.choose ((inGap_iff_before_firstHit b K k hk j.1).mp j.2)
#print axioms Paper7Lemma22Gaps.gapIndex

theorem gapIndex_spec (b : ℕ) (K : Finset (Fin b)) (k : Fin b) (hk : k ∈ K)
    (j : {j : Fin b // inGap b K k j}) :
    0 < gapIndex b K k hk j ∧ gapIndex b K k hk j < firstHitLength b K k hk ∧
      ((finRotate b) ^ gapIndex b K k hk j) k = j.1 :=
  Classical.choose_spec ((inGap_iff_before_firstHit b K k hk j.1).mp j.2)
#print axioms Paper7Lemma22Gaps.gapIndex_spec

theorem gapIndex_eq_of_rotate (b : ℕ) (K : Finset (Fin b)) (k : Fin b) (hk : k ∈ K)
    (j : {j : Fin b // inGap b K k j}) (t : ℕ)
    (ht : t < firstHitLength b K k hk) (he : ((finRotate b) ^ t) k = j.1) :
    gapIndex b K k hk j = t := by
  have hs := gapIndex_spec b K k hk j
  have hd := firstHitLength_le_card b K k hk
  exact rotate_pow_index_injective b k _ t (lt_of_lt_of_le hs.2.1 hd)
    (lt_of_lt_of_le ht hd) (hs.2.2.trans he.symm)
#print axioms Paper7Lemma22Gaps.gapIndex_eq_of_rotate

def zeroGapVector (b : ℕ) (q : Fin b → ℕ) (k : Fin b) (hk : k ∈ Kq b q)
    (a : ℝ) : Fin b → ℝ :=
  gapExtend b q k (fun j => zeroDirichletValue a (gapIndex b (Kq b q) k hk j))
#print axioms Paper7Lemma22Gaps.zeroGapVector

theorem zeroGapVector_not_mem (b : ℕ) (q : Fin b → ℕ) (k : Fin b)
    (hk : k ∈ Kq b q) (a : ℝ) (j : Fin b) (hj : ¬ inGap b (Kq b q) k j) :
    zeroGapVector b q k hk a j = 0 :=
  gapExtend_apply_not_mem b q k j _ hj
#print axioms Paper7Lemma22Gaps.zeroGapVector_not_mem

theorem zeroGapVector_along (b : ℕ) (q : Fin b → ℕ) (k : Fin b)
    (hk : k ∈ Kq b q) (a : ℝ) (heven : Even (firstHitLength b (Kq b q) k hk))
    (t : ℕ) (ht : t ≤ firstHitLength b (Kq b q) k hk) :
    zeroGapVector b q k hk a (((finRotate b) ^ t) k) = zeroDirichletValue a t := by
  by_cases h0 : t = 0
  · subst t
    have hn : ¬ inGap b (Kq b q) k k := fun h => (inGap_not_mem b _ k k h) hk
    simpa only [pow_zero, Equiv.Perm.one_apply, zeroDirichletValue_zero] using
      zeroGapVector_not_mem b q k hk a k hn
  · by_cases hd : t = firstHitLength b (Kq b q) k hk
    · subst t
      have hK := firstHitLength_mem b (Kq b q) k hk
      have hn : ¬ inGap b (Kq b q) k (((finRotate b) ^ firstHitLength b (Kq b q) k hk) k) :=
        fun h => (inGap_not_mem b _ k _ h) hK
      rw [zeroGapVector_not_mem b q k hk a _ hn]
      exact ((zeroDirichletValue_eq_zero_iff a _).mpr (Or.inl heven)).symm
    · have ht0 : 0 < t := Nat.pos_of_ne_zero h0
      have htd : t < firstHitLength b (Kq b q) k hk := by omega
      have hj := (inGap_iff_before_firstHit b (Kq b q) k hk
        (((finRotate b) ^ t) k)).mpr ⟨t, ht0, htd, rfl⟩
      unfold zeroGapVector
      rw [gapExtend_apply_mem b q k _ _ hj,
        gapIndex_eq_of_rotate b (Kq b q) k hk _ t htd rfl]
#print axioms Paper7Lemma22Gaps.zeroGapVector_along

theorem zeroGapVector_mem_kernel (b : ℕ) (q : Fin b → ℕ) (k : Fin b)
    (hk : k ∈ Kq b q) (a : ℝ) (heven : Even (firstHitLength b (Kq b q) k hk)) :
    zeroGapVector b q k hk a ∈ LinearMap.ker (Matrix.toLin' (Wmat b (fun _ => 0) q 0)) := by
  apply (mem_ker_Wmat_iff b (fun _ => 0) q 0 _).mpr
  intro j
  by_cases hq : 0 < q j
  · rw [ite_eq_left hq]
    have hj : j ∈ Kq b q := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hq⟩
    exact zeroGapVector_not_mem b q k hk a j (fun h => (inGap_not_mem b _ k j h) hj)
  · rw [ite_eq_right hq]
    simp only [zero_mul]
    have hj : j ∉ Kq b q := by
      simpa only [Kq, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    by_cases hg : inGap b (Kq b q) k j
    · obtain ⟨t, ht0, htd, he⟩ := (inGap_iff_before_firstHit b (Kq b q) k hk j).mp hg
      have hp : prv b j = ((finRotate b) ^ (t - 1)) k := by
        have hs := prv_rotate_pow_succ b k (t - 1)
        rw [show t - 1 + 1 = t by omega, he] at hs
        exact hs
      have hn : nxt b j = ((finRotate b) ^ (t + 1)) k := by
        rw [← he]
        exact nxt_rotate_pow b k t
      rw [hp, hn, zeroGapVector_along b q k hk a heven (t - 1) (by omega),
        zeroGapVector_along b q k hk a heven (t + 1) (by omega)]
      have hr := zeroDirichletValue_recurrence a (t - 1)
      simpa only [show t - 1 + 2 = t + 1 by omega] using hr
    · have hp : ¬ inGap b (Kq b q) k (prv b j) := by
        intro h
        have h' := inGap_next b (Kq b q) k (prv b j) hk h
          (by simpa only [nxt, prv, Equiv.apply_symm_apply] using hj)
        exact hg (by simpa only [nxt, prv, Equiv.apply_symm_apply] using h')
      have hn : ¬ inGap b (Kq b q) k (nxt b j) := by
        intro h
        have h' := inGap_prev b (Kq b q) k (nxt b j) hk h
          (by simpa only [nxt, prv, Equiv.symm_apply_apply] using hj)
        exact hg (by simpa only [nxt, prv, Equiv.symm_apply_apply] using h')
      rw [zeroGapVector_not_mem b q k hk a _ hp,
        zeroGapVector_not_mem b q k hk a _ hn, zero_add]
#print axioms Paper7Lemma22Gaps.zeroGapVector_mem_kernel

/-- Any actual zero-system solution obeys the finite Dirichlet recurrence up
through the next support vertex, not just through the gap's interior. -/
theorem zero_kernel_dirichlet (b : ℕ) (q : Fin b → ℕ) (k : Fin b)
    (hk : k ∈ Kq b q) (y : Fin b → ℝ)
    (hy : y ∈ LinearMap.ker (Matrix.toLin' (Wmat b (fun _ => 0) q 0))) :
    ∀ n : ℕ, n + 2 ≤ firstHitLength b (Kq b q) k hk →
      y (((finRotate b) ^ n) k) + y (((finRotate b) ^ (n + 2)) k) = 0 := by
  intro n hn
  have hm := firstHitLength_clear b (Kq b q) k hk (n + 1) (by omega) (by omega)
  have hr := kernel_recurrence_off_support b (fun _ => 0) q 0 y hy
    (((finRotate b) ^ (n + 1)) k) hm
  simpa only [prv_rotate_pow_succ, nxt_rotate_pow, zero_mul] using hr
#print axioms Paper7Lemma22Gaps.zero_kernel_dirichlet

theorem zero_gap_next_vanish_of_not_even (b : ℕ) (q : Fin b → ℕ) (k : Fin b)
    (hk : k ∈ Kq b q) (hodd : ¬ Even (firstHitLength b (Kq b q) k hk))
    (y : Fin b → ℝ) (hy : y ∈ LinearMap.ker (Matrix.toLin' (Wmat b (fun _ => 0) q 0))) :
    y (nxt b k) = 0 := by
  have h0 : y (((finRotate b) ^ 0) k) = 0 := by
    simpa using kernel_zero_on_support b (fun _ => 0) q 0 y hy k hk
  have hd := kernel_zero_on_support b (fun _ => 0) q 0 y hy
    (((finRotate b) ^ firstHitLength b (Kq b q) k hk) k)
    (firstHitLength_mem b (Kq b q) k hk)
  have he := (zeroDirichlet_right_endpoint (firstHitLength b (Kq b q) k hk)
    (fun n => y (((finRotate b) ^ n) k)) h0 (zero_kernel_dirichlet b q k hk y hy)).mp hd
  have h1 := he.resolve_left hodd
  simpa only [pow_one, nxt] using h1
#print axioms Paper7Lemma22Gaps.zero_gap_next_vanish_of_not_even

theorem zero_gapImage_eq_bot_of_not_even (b : ℕ) (q : Fin b → ℕ) (k : Fin b)
    (hk : k ∈ Kq b q) (hodd : ¬ Even (firstHitLength b (Kq b q) k hk)) :
    gapImage b (fun _ => 0) q 0 k = ⊥ := by
  apply (Submodule.eq_bot_iff (gapImage b (fun _ => 0) q 0 k)).mpr
  intro v hv
  obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp hv
  rw [← he]
  funext j
  exact vanish_on_gap b (fun _ => 0) q 0 y hy k hk
    (zero_gap_next_vanish_of_not_even b q k hk hodd y hy) j.1 j.2
#print axioms Paper7Lemma22Gaps.zero_gapImage_eq_bot_of_not_even

/-- Exact dimension of the original zero-gap image. -/
theorem zero_gapDim_eq (b : ℕ) (q : Fin b → ℕ) (hb : 3 ≤ b) (k : Fin b)
    (hk : k ∈ Kq b q) :
    gapDim b (fun _ => 0) q 0 k =
      if Even (firstHitLength b (Kq b q) k hk) then 1 else 0 := by
  classical
  by_cases he : Even (firstHitLength b (Kq b q) k hk)
  · rw [ite_eq_left he]
    have hle := gapDim_le_one b (fun _ => 0) q hb 0 k hk
    have hpos : 0 < gapDim b (fun _ => 0) q 0 k := by
      change 0 < Module.finrank ℝ (gapImage b (fun _ => 0) q 0 k)
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      let y := zeroGapVector b q k hk 1
      have hy : y ∈ LinearMap.ker (Matrix.toLin' (Wmat b (fun _ => 0) q 0)) :=
        zeroGapVector_mem_kernel b q k hk 1 he
      let v : gapImage b (fun _ => 0) q 0 k :=
        ⟨gapRestriction b q k y, Submodule.mem_map.mpr ⟨y, hy, rfl⟩⟩
      refine ⟨v, ?_⟩
      have hdpos := firstHitLength_pos b (Kq b q) k hk
      have hd2 : 1 < firstHitLength b (Kq b q) k hk := by
        obtain ⟨n, hn⟩ := he
        omega
      have hj : inGap b (Kq b q) k (nxt b k) :=
        (inGap_iff_before_firstHit b (Kq b q) k hk (nxt b k)).mpr
          ⟨1, by omega, hd2, by simp only [pow_one, nxt]⟩
      have hy1 : y (nxt b k) = 1 := by
        simpa only [pow_one, nxt, zeroDirichletValue_one] using
          zeroGapVector_along b q k hk 1 he 1 (by omega)
      intro hv
      have hz := congrArg (fun z : gapImage b (fun _ => 0) q 0 k => z.1 ⟨nxt b k, hj⟩) hv
      change y (nxt b k) = 0 at hz
      rw [hy1] at hz
      norm_num at hz
    omega
  · rw [ite_eq_right he]
    change Module.finrank ℝ (gapImage b (fun _ => 0) q 0 k) = 0
    exact Submodule.finrank_eq_zero.mpr (zero_gapImage_eq_bot_of_not_even b q k hk he)
#print axioms Paper7Lemma22Gaps.zero_gapDim_eq

end Paper7Lemma22Gaps
