import Mathlib

/-!
# The cut lemma

For a finite set `M`, a finite set `E` of unordered pairs (loops allowed) and `0 ≤ q ≤ 1`:
`∑_{X ⊆ M} q^{#(pairs of E not cut by X)} ≤ ∑_{X ⊆ M} q^{#(pairs of E cut by X)}`.
Proof: the two weights are `a - b χ_e(X)` and `a + b χ_e(X)` with `a = (1+q)/2`, `b = (1-q)/2`,
`χ_e(X) = ±1` (`-1` iff `X` cuts `e`); expanding the products over subsets `F ⊆ E`, the
coefficients are the character sums `∑_{X ⊆ M} ∏_{e ∈ F} χ_e(X) = ∏_{w ∈ M} (1 + (-1)^{k_w}) ≥ 0`,
and `(-b)^k ≤ b^k`.
-/

set_option autoImplicit false

open Finset

namespace P3SSSZ

section Cut

variable {α : Type*} [DecidableEq α]

/-- `X` cuts the unordered pair `e`: exactly one end of `e` lies in `X` (never for a loop). -/
def cut (X : Finset α) : Sym2 α → Bool :=
  Sym2.lift ⟨fun u v => xor (decide (u ∈ X)) (decide (v ∈ X)), fun _ _ => Bool.xor_comm _ _⟩

@[simp] theorem cut_mk (X : Finset α) (u v : α) :
    cut X s(u, v) = xor (decide (u ∈ X)) (decide (v ∈ X)) := rfl

/-- The sign `-1` on `X` and `+1` off `X`. -/
def sgn (X : Finset α) (w : α) : ℝ := if w ∈ X then -1 else 1

/-- `χ_e(X) = -1` if `X` cuts `e`, and `+1` otherwise. -/
def chi (X : Finset α) (e : Sym2 α) : ℝ := if cut X e then -1 else 1

theorem chi_mk (X : Finset α) (u v : α) : chi X s(u, v) = sgn X u * sgn X v := by
  unfold chi sgn
  by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;> simp [hu, hv]

theorem chi_eq (X : Finset α) (e : Sym2 α) : chi X e = sgn X e.out.1 * sgn X e.out.2 := by
  have h := chi_mk X e.out.1 e.out.2
  rwa [show s(e.out.1, e.out.2) = e from Quot.out_eq e] at h

theorem prod_sgn_comp {β : Type*} [DecidableEq β] (F : Finset β) (g : β → α) (X : Finset α) :
    ∏ e ∈ F, sgn X (g e) = ∏ w ∈ X, (-1 : ℝ) ^ #(F.filter fun e => g e = w) := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert e0 F he0 ih =>
    have hc : ∀ w, #((insert e0 F).filter fun e => g e = w) =
        #(F.filter fun e => g e = w) + if g e0 = w then 1 else 0 := by
      intro w
      rw [filter_insert]
      split_ifs with h
      · rw [card_insert_of_notMem (fun hm => he0 (mem_filter.mp hm).1)]
      · rw [add_zero]
    rw [prod_insert he0, ih]
    simp only [hc, pow_add, prod_mul_distrib, prod_pow_boole]
    rw [mul_comm]
    simp [sgn]

/-- Number of ends at `w` of the pairs of `F` (a loop at `w` counts twice). -/
noncomputable def ends (F : Finset (Sym2 α)) (w : α) : ℕ :=
  #(F.filter fun e => e.out.1 = w) + #(F.filter fun e => e.out.2 = w)

theorem prod_chi (F : Finset (Sym2 α)) (X : Finset α) :
    ∏ e ∈ F, chi X e = ∏ w ∈ X, (-1 : ℝ) ^ ends F w := by
  simp only [chi_eq, prod_mul_distrib, prod_sgn_comp F (fun e => e.out.1) X,
    prod_sgn_comp F (fun e => e.out.2) X, ends, pow_add]

/-- The character sums are nonnegative. -/
theorem charSum_nonneg (M : Finset α) (F : Finset (Sym2 α)) :
    0 ≤ ∑ X ∈ M.powerset, ∏ e ∈ F, chi X e := by
  simp only [prod_chi]
  rw [← prod_one_add (f := fun w => (-1 : ℝ) ^ ends F w) M]
  refine prod_nonneg fun w _ => ?_
  rcases neg_one_pow_eq_or ℝ (ends F w) with h | h <;> rw [h] <;> norm_num

/-- Expansion of `∏_e (a + t χ_e(X))` over subsets, summed over `X ⊆ M`. -/
theorem sum_prod_expand (M : Finset α) (E : Finset (Sym2 α)) (a t : ℝ) :
    ∑ X ∈ M.powerset, ∏ e ∈ E, (a + t * chi X e) =
      ∑ F ∈ E.powerset, t ^ #F * a ^ #(E \ F) * ∑ X ∈ M.powerset, ∏ e ∈ F, chi X e := by
  have h1 : ∀ X : Finset α, ∏ e ∈ E, (a + t * chi X e) =
      ∑ F ∈ E.powerset, t ^ #F * a ^ #(E \ F) * ∏ e ∈ F, chi X e := by
    intro X
    have h := prod_add (fun e => t * chi X e) (fun _ => a) E
    simp only [add_comm a]
    rw [h]
    refine sum_congr rfl fun F _ => ?_
    rw [prod_mul_distrib, prod_const, prod_const]
    ring
  simp only [h1]
  rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  rw [mul_sum]

theorem pow_card_uncut (X : Finset α) (E : Finset (Sym2 α)) (q : ℝ) :
    q ^ #(E.filter fun e => cut X e = false) =
      ∏ e ∈ E, ((1 + q) / 2 + (-((1 - q) / 2)) * chi X e) := by
  have h : ∀ e, ((1 + q) / 2 + (-((1 - q) / 2)) * chi X e) = if cut X e = true then 1 else q := by
    intro e
    unfold chi
    cases cut X e <;> simp <;> ring
  simp only [h]
  rw [prod_ite, prod_const_one, one_mul, prod_const]
  simp only [Bool.not_eq_true]

theorem pow_card_cut (X : Finset α) (E : Finset (Sym2 α)) (q : ℝ) :
    q ^ #(E.filter fun e => cut X e = true) =
      ∏ e ∈ E, ((1 + q) / 2 + ((1 - q) / 2) * chi X e) := by
  have h : ∀ e, ((1 + q) / 2 + ((1 - q) / 2) * chi X e) = if cut X e = true then q else 1 := by
    intro e
    unfold chi
    cases cut X e <;> simp <;> ring
  simp only [h]
  rw [prod_ite, prod_const_one, mul_one, prod_const]

/-- **Cut lemma.** -/
theorem cut_lemma (M : Finset α) (E : Finset (Sym2 α)) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ X ∈ M.powerset, q ^ #(E.filter fun e => cut X e = false) ≤
      ∑ X ∈ M.powerset, q ^ #(E.filter fun e => cut X e = true) := by
  simp only [pow_card_uncut, pow_card_cut, sum_prod_expand]
  apply sum_le_sum
  intro F _
  have hb : 0 ≤ (1 - q) / 2 := by linarith
  have ha : 0 ≤ ((1 + q) / 2) ^ #(E \ F) := pow_nonneg (by linarith) _
  have hk : (-((1 - q) / 2)) ^ #F ≤ ((1 - q) / 2) ^ #F := by
    calc (-((1 - q) / 2)) ^ #F ≤ |(-((1 - q) / 2)) ^ #F| := le_abs_self _
      _ = ((1 - q) / 2) ^ #F := by rw [abs_pow, abs_neg, abs_of_nonneg hb]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk ha) (charSum_nonneg M F)

end Cut

end P3SSSZ
