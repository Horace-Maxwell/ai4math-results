import Research.TaskH.General.ColorWordsStrict
import Research.TaskH.ColorWordsSaturation

/-!
Strict deleted-word counting for arbitrary k>=3. The generic tight-step and
rotation orbit replace every concrete finite prefix. The only case split on
colors concerns the two actual ranks exchanged, never all k colors.
-/

set_option autoImplicit false

namespace TaskH.General.ColorWords

open _root_.TaskH.ColorWords

variable {k : ℕ}

/-- Exchange the first two actual ranks, with positivity derived from hk. -/
def swapFirstTwo (hk : 3 ≤ k) : Equiv.Perm (Fin k) :=
  Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩

theorem swap_step_le (hk : 3 ≤ k) (x y : Fin k)
    (hnot : ¬ (x.val = 1 ∧ y.val = 0)) :
    (if y < x then 1 else 0 : ℕ) ≤
      if swapFirstTwo hk y < swapFirstTwo hk x then 1 else 0 := by
  unfold swapFirstTwo
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.ext_iff, Fin.lt_def] at * <;> omega

theorem swap_increasing_nonzero (hk : 3 ≤ k) (x y : Fin k)
    (hx : x.val ≠ 0) (hy : y.val ≠ 0) (hxy : x < y) :
    swapFirstTwo hk x < swapFirstTwo hk y := by
  unfold swapFirstTwo
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.ext_iff, Fin.lt_def] at * <;> omega

/-- One strict local gain and no local losses give a strict total gain. -/
theorem descents_lt_of_steps (w z : ℕ → Fin k) (L : ℕ)
    (hle : ∀ i < L,
      (if w (i + 1) < w i then 1 else 0 : ℕ) ≤
        if z (i + 1) < z i then 1 else 0)
    (hstrict : ∃ j < L,
      (if w (j + 1) < w j then 1 else 0 : ℕ) <
        if z (j + 1) < z j then 1 else 0) :
    descents w L < descents z L := by
  revert hle hstrict
  induction L with
  | zero => rintro _ ⟨j, hj, _⟩; omega
  | succ L ih =>
    intro hle hstrict
    obtain ⟨j, hj, hgain⟩ := hstrict
    rw [descents_succ, descents_succ]
    by_cases hjL : j < L
    · have hi := ih (fun i hi => hle i (by omega)) ⟨j, hjL, hgain⟩
      have hs := hle L (by omega)
      omega
    · have he : j = L := by omega
      subst j
      have hi := _root_.TaskH.ColorWords.descents_mono_of_steps w z L
        (fun i hi => hle i (by omega))
      omega

/-- The missing rank zero makes endpoint capacity tight. -/
theorem tight_of_first_nonzero (hk : 3 ≤ k) (w : ℕ → Fin k) (L b : ℕ)
    (hlen : L + 2 = k * (b + 1))
    (hne : ∀ i < L, w i ≠ w (i + 1))
    (hcount : descents w L ≤ b) (hfirst : (w 0).val ≠ 0) :
    descents w L = b ∧
      L + (w 0).val = (w L).val + k * descents w L := by
  have hc := endpoint_capacity w L hne
  have hlast := (w L).isLt
  have hlen' : L + 2 = k * b + k := by
    simpa only [Nat.mul_add, Nat.mul_one] using hlen
  have hmul := Nat.mul_le_mul_left k hcount
  have he : k * descents w L = k * b := by omega
  have hbD : b ≤ descents w L := le_of_mul_le_mul_left he.ge (by omega : 0 < k)
  have hd : descents w L = b := by omega
  exact ⟨hd, by omega⟩

/-- Tight words have a real 0→1 edge and no 1→0 edge. -/
theorem swap_exceeds_budget (hk : 3 ≤ k) (w : ℕ → Fin k) (L b : ℕ)
    (hlen : L + 2 = k * (b + 1)) (hb : 1 ≤ b)
    (hne : ∀ i < L, w i ≠ w (i + 1))
    (hcount : descents w L ≤ b) (hfirst : (w 0).val ≠ 0) :
    b < descents (fun i => swapFirstTwo hk (w i)) L := by
  obtain ⟨hd, htight⟩ := tight_of_first_nonzero hk w L b hlen hne hcount hfirst
  have hmul : k ≤ k * b := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left k hb
  have hkL : k ≤ L := by
    have he : L + 2 = k * b + k := by
      simpa only [Nat.mul_add, Nat.mul_one] using hlen
    omega
  obtain ⟨j, hj0⟩ := tight_prefix_surjective hk w L hkL hne htight
    (⟨0, by omega⟩ : Fin k)
  have hj : j.val < L := by have := j.isLt; omega
  have hz0 : (w j.val).val = 0 := congrArg Fin.val hj0
  have hz1 : (w (j.val + 1)).val = 1 := by
    have hs := _root_.TaskH.ColorWords.tight_step w L hne htight j.val hj
    change 1 + (w j.val).val = (w (j.val + 1)).val +
      k * (if w (j.val + 1) < w j.val then 1 else 0) at hs
    rw [hz0] at hs
    split_ifs at hs <;> omega
  have hno : ∀ i < L, ¬ ((w i).val = 1 ∧ (w (i + 1)).val = 0) := by
    intro i hi hbad
    have hs := _root_.TaskH.ColorWords.tight_step w L hne htight i hi
    obtain ⟨h1, h0⟩ := hbad
    change 1 + (w i).val = (w (i + 1)).val +
      k * (if w (i + 1) < w i then 1 else 0) at hs
    rw [h1, h0] at hs
    split_ifs at hs; omega
  have hgain : (if w (j.val + 1) < w j.val then 1 else 0 : ℕ) <
      if swapFirstTwo hk (w (j.val + 1)) < swapFirstTwo hk (w j.val)
      then 1 else 0 := by
    have he0 : w j.val = (⟨0, by omega⟩ : Fin k) := Fin.ext hz0
    have he1 : w (j.val + 1) = (⟨1, by omega⟩ : Fin k) := Fin.ext hz1
    rw [he0, he1]
    norm_num [swapFirstTwo, Fin.lt_def]
  have hlt := descents_lt_of_steps w (fun i => swapFirstTwo hk (w i)) L
    (fun i hi => swap_step_le hk (w i) (w (i + 1)) (hno i hi))
    ⟨j.val, hj, hgain⟩
  omega

/-- A long deleted word has strictly fewer than k good orders. -/
theorem low_descent_orders_card_lt (hk : 3 ≤ k) (w : ℕ → Fin k) (L b : ℕ)
    (hlen : L + 2 = k * (b + 1)) (hb : 1 ≤ b)
    (hne : ∀ i < L, w i ≠ w (i + 1)) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
      descents (fun i => π (w i)) L ≤ b)).card < k := by
  classical
  let S : Finset (Equiv.Perm (Fin k)) := Finset.univ.filter
    (fun π => descents (fun i => π (w i)) L ≤ b)
  change S.card < k
  have hle : S.card ≤ k := low_descent_orders_card_le hk w L b hlen hne
  by_contra hn
  have hcard : S.card = k := by omega
  obtain ⟨π₀, hπ₀⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  let f : Fin (k - 1) → Fin k := fun i => w i.val
  have hf : Function.Injective f := ranked_prefix_injective hk w π₀ L b hlen hne
    (Finset.mem_filter.mp hπ₀).2
  obtain ⟨β, hmissing, hcover⟩ := exists_missing_prefix_color (by omega) f hf
  have hmono : ∀ π ∈ S, StrictMono (fun i => π (f i)) := by
    intro π hπ
    exact ranked_prefix_strictMono hk w π L b hlen hne (Finset.mem_filter.mp hπ).2
  have hinj : Set.InjOn (fun π : Equiv.Perm (Fin k) => π β) (S : Set _) := by
    intro π hπ ρ hρ he
    exact perm_eq_of_missing_rank f β hmissing hcover π ρ (hmono π hπ) (hmono ρ hρ) he
  have hsurj : Set.SurjOn (fun π : Equiv.Perm (Fin k) => π β)
      (S : Set _) ((Finset.univ : Finset (Fin k)) : Set _) := by
    apply Finset.surjOn_of_injOn_of_card_le _ (fun _ _ => Finset.mem_univ _) hinj
    simpa only [Finset.card_univ, Fintype.card_fin, hcard] using (Nat.le_refl k)
  obtain ⟨π, hπ, hπβ⟩ := hsurj (Finset.mem_univ (⟨0, by omega⟩ : Fin k))
  obtain ⟨ρ, hρ, hρβ⟩ := hsurj (Finset.mem_univ (⟨1, by omega⟩ : Fin k))
  change π β = (⟨0, by omega⟩ : Fin k) at hπβ
  change ρ β = (⟨1, by omega⟩ : Fin k) at hρβ
  let κ : Equiv.Perm (Fin k) := π.trans (swapFirstTwo hk)
  have hnonzero : ∀ i, (π (f i)).val ≠ 0 := by
    intro i he
    apply hmissing i
    apply π.injective
    exact (Fin.ext he).trans hπβ.symm
  have hκmono : StrictMono (fun i => κ (f i)) := by
    intro i j hij
    change swapFirstTwo hk (π (f i)) < swapFirstTwo hk (π (f j))
    exact swap_increasing_nonzero hk _ _ (hnonzero i) (hnonzero j) (hmono π hπ hij)
  have hκβ : κ β = (⟨1, by omega⟩ : Fin k) := by
    change swapFirstTwo hk (π β) = _
    rw [hπβ]
    exact Equiv.swap_apply_left _ _
  have hκρ : κ = ρ := perm_eq_of_missing_rank f β hmissing hcover κ ρ
    hκmono (hmono ρ hρ) (hκβ.trans hρβ.symm)
  have hswaplow : descents (fun i => swapFirstTwo hk (π (w i))) L ≤ b := by
    change descents (fun i => κ (w i)) L ≤ b
    rw [hκρ]
    exact (Finset.mem_filter.mp hρ).2
  have hfirst : (π (w 0)).val ≠ 0 := hnonzero ⟨0, by omega⟩
  have hhigh := swap_exceeds_budget hk (fun i => π (w i)) L b hlen hb
    (fun i hi => π.injective.ne (hne i hi)) (Finset.mem_filter.mp hπ).2 hfirst
  omega

end TaskH.General.ColorWords

#print axioms TaskH.General.ColorWords.swapFirstTwo
#print axioms TaskH.General.ColorWords.swap_step_le
#print axioms TaskH.General.ColorWords.swap_increasing_nonzero
#print axioms TaskH.General.ColorWords.descents_lt_of_steps
#print axioms TaskH.General.ColorWords.tight_of_first_nonzero
#print axioms TaskH.General.ColorWords.swap_exceeds_budget
#print axioms TaskH.General.ColorWords.low_descent_orders_card_lt
