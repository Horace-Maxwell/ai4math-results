import Research.Backfill.Paper7.Lemma22EmptyQ

/-! Actual single-gap and global dimension bounds. No gap decomposition or
parity-count identity is assumed. This file is an uncompiled source candidate. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix BigOperators

namespace Paper7Lemma22Gaps
open BackfillPaper7.Challenge
open Fin.NatCast

theorem nxt_rotate_pow (b : ℕ) (k : Fin b) (n : ℕ) :
    nxt b (((finRotate b) ^ n) k) = ((finRotate b) ^ (n + 1)) k := by
  simp only [nxt, pow_succ', Equiv.Perm.mul_apply]
#print axioms Paper7Lemma22Gaps.nxt_rotate_pow

theorem prv_rotate_pow_succ (b : ℕ) (k : Fin b) (n : ℕ) :
    prv b (((finRotate b) ^ (n + 1)) k) = ((finRotate b) ^ n) k := by
  rw [← nxt_rotate_pow]
  exact (finRotate b).symm_apply_apply _
#print axioms Paper7Lemma22Gaps.prv_rotate_pow_succ

theorem rotate_pow_apply (b : ℕ) [NeZero b] (k : Fin b) (n : ℕ) :
    ((finRotate b) ^ n) k = k + (n : Fin b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, finRotate_apply]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]
#print axioms Paper7Lemma22Gaps.rotate_pow_apply

theorem rotate_reaches (b : ℕ) (k j : Fin b) :
    ∃ n : ℕ, ((finRotate b) ^ n) k = j := by
  let : NeZero b := k.neZero
  refine ⟨(j - k).val, ?_⟩
  rw [rotate_pow_apply, Fin.cast_val_eq_self]
  exact add_sub_cancel k j
#print axioms Paper7Lemma22Gaps.rotate_reaches

theorem kernel_zero_on_support (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (y : Fin b → ℝ) (hy : y ∈ LinearMap.ker (Matrix.toLin' (Wmat b p q ε)))
    (k : Fin b) (hk : k ∈ Kq b q) : y k = 0 := by
  have hq : 0 < q k := (Finset.mem_filter.mp hk).2
  have h := (mem_ker_Wmat_iff b p q ε y).mp hy k
  simpa only [hq, ite_true] using h
#print axioms Paper7Lemma22Gaps.kernel_zero_on_support

theorem kernel_recurrence_off_support (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (y : Fin b → ℝ) (hy : y ∈ LinearMap.ker (Matrix.toLin' (Wmat b p q ε)))
    (k : Fin b) (hk : k ∉ Kq b q) :
    y (prv b k) + y (nxt b k) = ε * (1 - (p k : ℝ)) * y k := by
  have hq : ¬ 0 < q k := by simpa only [Kq, Finset.mem_filter, Finset.mem_univ, true_and] using hk
  have h := (mem_ker_Wmat_iff b p q ε y).mp hy k
  simpa only [hq, ite_false] using h
#print axioms Paper7Lemma22Gaps.kernel_recurrence_off_support

theorem inGap_next_not_mem (b : ℕ) (K : Finset (Fin b)) (k j : Fin b)
    (h : inGap b K k j) : nxt b k ∉ K := by
  obtain ⟨d, hd, _, hclear⟩ := h
  have h1 := hclear 1 (Finset.mem_Icc.mpr ⟨le_rfl, (Finset.mem_Icc.mp hd).1⟩)
  simpa only [pow_one, nxt] using h1
#print axioms Paper7Lemma22Gaps.inGap_next_not_mem

theorem next_mem_gap (b : ℕ) (hb : 3 ≤ b) (K : Finset (Fin b)) (k : Fin b)
    (hk : nxt b k ∉ K) : inGap b K k (nxt b k) := by
  refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_, ?_⟩
  · simp only [pow_one, nxt]
  · intro d hd
    have he : d = 1 := by have := Finset.mem_Icc.mp hd; omega
    subst d
    simpa only [pow_one, nxt] using hk
#print axioms Paper7Lemma22Gaps.next_mem_gap

/-- A recurrence solution vanishes along any clear segment when its first two
values vanish. The segment length is the actual witness in frozen inGap. -/
theorem vanish_clear_segment (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (y : Fin b → ℝ) (hy : y ∈ LinearMap.ker (Matrix.toLin' (Wmat b p q ε)))
    (k : Fin b) (h0 : y k = 0) (h1 : y (nxt b k) = 0) :
    ∀ n : ℕ, (∀ d ∈ Finset.Icc 1 n, ((finRotate b) ^ d) k ∉ Kq b q) →
      y (((finRotate b) ^ n) k) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hclear
    cases n with
    | zero => simpa using h0
    | succ n =>
      cases n with
      | zero => simpa only [Nat.zero_add, pow_one, nxt] using h1
      | succ n =>
        have hz0 : y (((finRotate b) ^ n) k) = 0 := ih n (by omega) (by
          intro d hd
          exact hclear d (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, by
            have := (Finset.mem_Icc.mp hd).2; omega⟩))
        have hz1 : y (((finRotate b) ^ (n + 1)) k) = 0 := ih (n + 1) (by omega) (by
          intro d hd
          exact hclear d (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, by
            have := (Finset.mem_Icc.mp hd).2; omega⟩))
        have hmid := hclear (n + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hr := kernel_recurrence_off_support b p q ε y hy
          (((finRotate b) ^ (n + 1)) k) hmid
        rw [prv_rotate_pow_succ, nxt_rotate_pow, hz0, hz1, mul_zero, zero_add] at hr
        exact hr
#print axioms Paper7Lemma22Gaps.vanish_clear_segment

theorem vanish_on_gap (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (y : Fin b → ℝ) (hy : y ∈ LinearMap.ker (Matrix.toLin' (Wmat b p q ε)))
    (k : Fin b) (hk : k ∈ Kq b q) (h1 : y (nxt b k) = 0)
    (j : Fin b) (hj : inGap b (Kq b q) k j) : y j = 0 := by
  obtain ⟨d, _, rfl, hclear⟩ := hj
  exact vanish_clear_segment b p q ε y hy k
    (kernel_zero_on_support b p q ε y hy k hk) h1 d hclear
#print axioms Paper7Lemma22Gaps.vanish_on_gap

/-- The original gap restriction image has dimension at most one, for every ε. -/
theorem gapDim_le_one (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℝ) (k : Fin b) (hk : k ∈ Kq b q) : gapDim b p q ε k ≤ 1 := by
  classical
  let J := {j : Fin b // inGap b (Kq b q) k j}
  let S : Submodule ℝ (J → ℝ) :=
    (LinearMap.ker (Matrix.toLin' (Wmat b p q ε))).map
      (LinearMap.funLeft ℝ ℝ (fun j : J => j.val))
  change Module.finrank ℝ S ≤ 1
  by_cases hn : nxt b k ∈ Kq b q
  · have hempty : IsEmpty J := ⟨fun j => (inGap_next_not_mem b (Kq b q) k j.1 j.2) hn⟩
    let : IsEmpty J := hempty
    exact S.finrank_le.trans (by simp)
  · let j0 : J := ⟨nxt b k, next_mem_gap b hb (Kq b q) k hn⟩
    let ev : S →ₗ[ℝ] ℝ := (LinearMap.proj j0).comp S.subtype
    have hz : ∀ u : S, ev u = 0 → u = 0 := by
      intro u hu
      obtain ⟨y, hy, hyu⟩ := Submodule.mem_map.mp u.property
      have hy1 : y (nxt b k) = 0 := by
        have hh := congrFun hyu j0
        change y (nxt b k) = u.1 j0 at hh
        change u.1 j0 = 0 at hu
        exact hh.trans hu
      apply Subtype.ext
      funext j
      change u.1 j = 0
      calc
        u.1 j = y j.1 := (congrFun hyu j).symm
        _ = 0 := vanish_on_gap b p q ε y hy k hk hy1 j.1 j.2
    have hinj : Function.Injective ev := by
      intro u v huv
      exact sub_eq_zero.mp (hz (u - v) (by rw [map_sub, huv, sub_self]))
    simpa only [Module.finrank_self] using ev.finrank_le_finrank_of_injective hinj
#print axioms Paper7Lemma22Gaps.gapDim_le_one

/-- Successor values at all constrained vertices determine the whole solution. -/
theorem zero_of_support_successors (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (hK : (Kq b q).Nonempty) (y : Fin b → ℝ)
    (hy : y ∈ LinearMap.ker (Matrix.toLin' (Wmat b p q ε)))
    (hnext : ∀ k ∈ Kq b q, y (nxt b k) = 0) : y = 0 := by
  obtain ⟨k, hk⟩ := hK
  have hz : ∀ n : ℕ, y (((finRotate b) ^ n) k) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa using kernel_zero_on_support b p q ε y hy k hk
      | succ n =>
        cases n with
        | zero => simpa only [Nat.zero_add, pow_one, nxt] using hnext k hk
        | succ n =>
          by_cases hmid : ((finRotate b) ^ (n + 1)) k ∈ Kq b q
          · simpa only [nxt_rotate_pow] using hnext _ hmid
          · have hr := kernel_recurrence_off_support b p q ε y hy
              (((finRotate b) ^ (n + 1)) k) hmid
            rw [prv_rotate_pow_succ, nxt_rotate_pow,
              ih n (by omega), ih (n + 1) (by omega), mul_zero, zero_add] at hr
            exact hr
  funext j
  obtain ⟨n, hn⟩ := rotate_reaches b k j
  change y j = 0
  simpa only [hn] using hz n
#print axioms Paper7Lemma22Gaps.zero_of_support_successors

def supportSuccessorMap (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ) :
    LinearMap.ker (Matrix.toLin' (Wmat b p q ε)) →ₗ[ℝ]
      ({k : Fin b // k ∈ Kq b q} → ℝ) where
  toFun y k := y.1 (nxt b k.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#print axioms Paper7Lemma22Gaps.supportSuccessorMap

theorem supportSuccessorMap_injective (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (hK : (Kq b q).Nonempty) : Function.Injective (supportSuccessorMap b p q ε) := by
  intro u v huv
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply zero_of_support_successors b p q ε hK (u.1 - v.1)
    ((LinearMap.ker (Matrix.toLin' (Wmat b p q ε))).sub_mem u.property v.property)
  intro k hk
  have h := congrFun huv ⟨k, hk⟩
  change u.1 (nxt b k) = v.1 (nxt b k) at h
  change u.1 (nxt b k) - v.1 (nxt b k) = 0
  exact sub_eq_zero.mpr h
#print axioms Paper7Lemma22Gaps.supportSuccessorMap_injective

theorem deltaE_nonempty_bound (b : ℕ) (p q : Fin b → ℕ) (ε : ℝ)
    (hK : (Kq b q).Nonempty) : deltaE b p q ε ≤ (Kq b q).card := by
  have h := (supportSuccessorMap b p q ε).finrank_le_finrank_of_injective
    (supportSuccessorMap_injective b p q ε hK)
  simpa only [deltaE, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h
#print axioms Paper7Lemma22Gaps.deltaE_nonempty_bound

end Paper7Lemma22Gaps
