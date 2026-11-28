import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic

namespace StanleyContinuation
noncomputable section
open Finset

def shadeWeight {k : ℕ} (q : ℕ) (s h : Fin k → ℕ) :=
  ∏ i, q ^ h i * (q-1) ^ (s i - h i)

private def normWeight {k : ℕ} (q : ℕ) (s h : Fin k → ℕ) :=
  ∏ i, q ^ (h i - 1) * (q-1) ^ (s i - h i)

private def diagWeight {k : ℕ} (q : ℕ) (s : Fin k → ℕ) :=
  ∏ i, (q-1) ^ (s i - 1)

private theorem shade_factor {k q : ℕ} (s h : Fin k → ℕ) (hp : ∀ i, 0 < h i) :
    shadeWeight q s h = q ^ k * normWeight q s h := by
  classical
  calc
    _ = ∏ i, q * (q ^ (h i - 1) * (q-1) ^ (s i - h i)) := by
      unfold shadeWeight
      apply prod_congr rfl
      intro i _
      have hh : h i = (h i - 1) + 1 := by have := hp i; omega
      conv_lhs => arg 1; rw [hh, pow_succ]
      ac_rfl
    _ = _ := by simp [prod_mul_distrib, normWeight]

private theorem norm_mod {k q : ℕ} (s h : Fin k → ℕ) (hp : ∀ i, 0 < h i) :
    normWeight q s h ≡ (if ∀ i, h i = 1 then diagWeight q s else 0) [MOD q] := by
  classical
  split_ifs with h1
  · simp [normWeight, diagWeight, h1, Nat.ModEq]
  · push Not at h1
    obtain ⟨i,hi⟩ := h1
    apply Nat.modEq_zero_iff_dvd.mpr
    unfold normWeight
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (mem_univ i))
    exact dvd_mul_of_dvd_left (dvd_pow_self q (by have := hp i; omega)) _

private def goodRows {k : ℕ} {α : Type*} [Fintype α] (r : α → Fin k → ℕ) :=
  Finset.univ.filter (fun a => ∀ i, r a i = 1)

private theorem total_mod {k q : ℕ} {α : Type*} [Fintype α] (s : Fin k → ℕ)
    (r : α → Fin k → ℕ) (hp : ∀ a i, 0 < r a i) :
    (∑ a, normWeight q s (r a)) ≡ (goodRows r).card * diagWeight q s [MOD q] := by
  classical
  calc
    _ ≡ ∑ a, (if ∀ i, r a i = 1 then diagWeight q s else 0) [MOD q] :=
      Nat.ModEq.sum fun a _ => norm_mod s (r a) (hp a)
    _ = _ := by simp [goodRows, ← sum_filter]

private theorem total_factor {k : ℕ} {γ : Type*} [Fintype γ]
    (q : ℕ) (s : Fin k → ℕ) (u : γ → Fin k → ℕ) (hu : ∀ a i, 0 < u a i) :
    (∑ a, shadeWeight q s (u a)) = q ^ k * ∑ a, normWeight q s (u a) := by
  rw [mul_sum]
  exact sum_congr rfl (fun a _ => shade_factor s (u a) (hu a))

theorem recover_rows {k : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (s : Fin k → ℕ) (r : α → Fin k → ℕ) (t : β → Fin k → ℕ)
    (hr : ∀ a i, 0 < r a i) (ht : ∀ b i, 0 < t b i)
    (he : ∀ q ≥ 2, (∑ a, shadeWeight q s (r a)) = ∑ b, shadeWeight q s (t b)) :
    (Finset.univ.filter (fun a => ∀ i, r a i = 1)).card =
      (Finset.univ.filter (fun b => ∀ i, t b i = 1)).card := by
  classical
  let q := 2 + (goodRows r).card + (goodRows t).card
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hsum := ((total_factor q s r hr).symm.trans (he q hq)).trans (total_factor q s t ht)
  have heq := Nat.eq_of_mul_eq_mul_left (pow_pos (by omega : 0 < q) k) hsum
  have hmod := (total_mod (q:=q) s r hr).symm.trans
    ((heq.symm ▸ total_mod (q:=q) s t ht : (∑ a, normWeight q s (r a)) ≡ (goodRows t).card * diagWeight q s [MOD q]))
  have hcop : q.Coprime (diagWeight q s) := by
    apply Nat.coprime_fintype_prod_right_iff.mpr
    intro i
    exact ((Nat.coprime_self_sub_right (by omega : 1 ≤ q)).mpr (Nat.coprime_one_right q)).pow_right _
  exact (Nat.ModEq.cancel_right_of_coprime hcop hmod).eq_of_lt_of_lt
    (by dsimp [q]; omega) (by dsimp [q]; omega)

end
end StanleyContinuation
