import Research.Backfill.Paper7.EightUnitResidual
import Research.Backfill.Paper7.EightPathUnitArithmetic
import Research.Backfill.Paper7.EightAlternatingTransfer
import Research.Backfill.Paper7.DihedralOrbitBasics

/-! NEW SOURCE ONLY repair after development 441. The original five
headers and alternating-support load range are unchanged. This source
has not been compiled; all default budgets and linters remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem punctured_successor_ne_zero (p : Fin 8 → ℕ) (y : Fin 8 → ℝ)
    (k : Fin 8) (hy : y ≠ 0) (hyk : y k = 0)
    (hr : ∀ i, i ≠ k → unitResidual p y i = 0) : y (nxt 8 k) ≠ 0 := by
  let q : Fin 8 → ℕ := fun i => if i = k then 1 else 0
  have hK : Kq 8 q = {k} := by
    ext i
    by_cases hi : i = k <;> simp [Kq,q,hi]
  have hker : y ∈ LinearMap.ker (Matrix.toLin' (Wmat 8 p q 1)) := by
    apply (Paper7Lemma22Gaps.mem_ker_Wmat_iff 8 p q 1 y).mpr
    intro i
    by_cases hi : i = k
    · subst i; simpa [q] using hyk
    · have hh := hr i hi
      simp only [unitResidual_apply] at hh
      simp only [q,hi,ite_false,lt_self_iff_false,one_mul]
      linarith only [hh]
  intro hn
  apply hy
  apply Paper7Lemma22Gaps.zero_of_support_successors 8 p q 1
    (by rw [hK]; exact Finset.singleton_nonempty k) y hker
  intro i hi
  have hik : i = k := by simpa only [hK,Finset.mem_singleton] using hi
  simpa only [hik] using hn
#print axioms Paper7EightCycle.punctured_successor_ne_zero

theorem punctured_even_zero_load (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) (hcap : ∀ i, p i ≤ 13)
    (y : Fin 8 → ℝ) (hy : y ≠ 0) (hz : y 0 = 0)
    (hr : ∀ i, i ≠ 0 → unitResidual p y i = 0) : (∑ i, p i) ≤ 15 := by
  have hp1 := ho 1 (by decide)
  have hp3 := ho 3 (by decide)
  have hp5 := ho 5 (by decide)
  have hp7 := ho 7 (by decide)
  have h1 := hr 1 (by decide)
  have h2 := hr 2 (by decide)
  have h3 := hr 3 (by decide)
  have h4 := hr 4 (by decide)
  have h5 := hr 5 (by decide)
  have h6 := hr 6 (by decide)
  have h7 := hr 7 (by decide)
  norm_num [unitResidual_apply,prv,nxt,hp1,hp3,hp5,hp7,hz] at h1 h2 h3 h4 h5 h6 h7
  have hn1 : y 1 ≠ 0 := by
    simpa [nxt] using punctured_successor_ne_zero p y 0 hy hz hr
  have hn2 : y 2 ≠ 0 := by intro hh; apply hn1; linarith only [h1,hh]
  have e0 : ((p 2 : ℝ)+1)*y 2+y 4 = 0 := by nlinarith only [h1,h2,h3]
  have e1 : y 2+((p 4 : ℝ)+1)*y 4+y 6 = 0 := by nlinarith only [h3,h4,h5]
  have e2 : y 4+((p 6 : ℝ)+1)*y 6 = 0 := by nlinarith only [h5,h6,h7]
  have he : (((p 2 : ℝ)+1)*((p 4 : ℝ)+1)*((p 6 : ℝ)+1)
      -((p 2 : ℝ)+1)-((p 6 : ℝ)+1))*y 2 = 0 := by
    linear_combination (((p 4 : ℝ)+1)*((p 6 : ℝ)+1)-1)*e0 - ((p 6 : ℝ)+1)*e1 + e2
  have he0 := (mul_eq_zero.mp he).resolve_right hn2
  have heR : ((p 2 : ℝ)+1)*((p 4 : ℝ)+1)*((p 6 : ℝ)+1) =
      ((p 2 : ℝ)+1)+((p 6 : ℝ)+1) := by linarith only [he0]
  have heZ : ((p 2 : ℤ)+1)*((p 4 : ℤ)+1)*((p 6 : ℤ)+1) =
      ((p 2 : ℤ)+1)+((p 6 : ℤ)+1) := by exact_mod_cast heR
  have hs := positive_three_continuant_sum ((p 2 : ℤ)+1) ((p 4 : ℤ)+1)
    ((p 6 : ℤ)+1) (by omega) (by omega) (by omega) heZ
  have hsmall : p 2+p 4+p 6 ≤ 2 := by omega
  rw [eight_alternating_sum p ho]
  have hc := hcap 0
  omega
#print axioms Paper7EightCycle.punctured_even_zero_load

theorem punctured_odd_one_load (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) (hcap : ∀ i, p i ≤ 13)
    (y : Fin 8 → ℝ) (hy : y ≠ 0) (hz : y 1 = 0)
    (hr : ∀ i, i ≠ 1 → unitResidual p y i = 0) : (∑ i, p i) ≤ 15 := by
  have hp3 := ho 3 (by decide)
  have hp5 := ho 5 (by decide)
  have hp7 := ho 7 (by decide)
  have h0 := hr 0 (by decide)
  have h2 := hr 2 (by decide)
  have h3 := hr 3 (by decide)
  have h4 := hr 4 (by decide)
  have h5 := hr 5 (by decide)
  have h6 := hr 6 (by decide)
  have h7 := hr 7 (by decide)
  norm_num [unitResidual_apply,prv,nxt,hp3,hp5,hp7,hz] at h0 h2 h3 h4 h5 h6 h7
  have hneg : (-1 : Fin 8) = 7 := by decide
  rw [hneg] at h0
  have hn2 : y 2 ≠ 0 := by
    simpa [nxt] using punctured_successor_ne_zero p y 1 hy hz hr
  have e0 : (p 2 : ℝ)*y 2+y 4 = 0 := by nlinarith only [h2,h3]
  have e1 : y 2+((p 4 : ℝ)+1)*y 4+y 6 = 0 := by nlinarith only [h3,h4,h5]
  have e2 : y 4+((p 6 : ℝ)+1)*y 6+y 0 = 0 := by nlinarith only [h5,h6,h7]
  have e3 : y 6+(p 0 : ℝ)*y 0 = 0 := by nlinarith only [h7,h0]
  have he : ((p 2 : ℝ)*((p 4 : ℝ)+1)*((p 6 : ℝ)+1)*(p 0 : ℝ)
      -(p 2 : ℝ)*((p 4 : ℝ)+1)-(p 2 : ℝ)*(p 0 : ℝ)
      -((p 6 : ℝ)+1)*(p 0 : ℝ)+1)*y 2 = 0 := by
    linear_combination (((p 4 : ℝ)+1)*((p 6 : ℝ)+1)*(p 0 : ℝ)
      -((p 4 : ℝ)+1)-(p 0 : ℝ))*e0 + (1-((p 6 : ℝ)+1)*(p 0 : ℝ))*e1
      + (p 0 : ℝ)*e2 - e3
  have he0 := (mul_eq_zero.mp he).resolve_right hn2
  have heZ : (p 2 : ℤ)*((p 4 : ℤ)+1)*((p 6 : ℤ)+1)*(p 0 : ℤ)
      -(p 2 : ℤ)*((p 4 : ℤ)+1)-(p 2 : ℤ)*(p 0 : ℤ)
      -((p 6 : ℤ)+1)*(p 0 : ℤ)+1 = 0 := by exact_mod_cast he0
  rw [eight_alternating_sum p ho]
  by_cases hp2 : p 2 = 0
  · have hmul : ((p 6 : ℤ)+1)*(p 0 : ℤ) = 1 := by
      rw [hp2] at heZ
      norm_num at heZ
      linarith only [heZ]
    have hp0 : (p 0 : ℤ) ≥ 1 := by
      by_contra hh
      have hz0 : p 0 = 0 := by omega
      rw [hz0] at hmul
      norm_num at hmul
    have hh := mul_nonneg (show 0 ≤ (p 6 : ℤ) by omega)
      (show 0 ≤ (p 0 : ℤ)-1 by omega)
    have hc := hcap 4
    have hs : (p 6 : ℤ)+(p 0 : ℤ) ≤ 1 := by nlinarith only [hmul,hh]
    omega
  by_cases hp0 : p 0 = 0
  · have hmul : (p 2 : ℤ)*((p 4 : ℤ)+1) = 1 := by
      rw [hp0] at heZ
      norm_num at heZ
      linarith only [heZ]
    have hh := mul_nonneg (show 0 ≤ (p 4 : ℤ) by omega)
      (show 0 ≤ (p 2 : ℤ)-1 by omega)
    have hc := hcap 6
    have hs : (p 2 : ℤ)+(p 4 : ℤ) ≤ 1 := by nlinarith only [hmul,hh]
    omega
  have hs := positive_four_continuant_sum (p 2 : ℤ) ((p 4 : ℤ)+1)
    ((p 6 : ℤ)+1) (p 0 : ℤ) (by omega) (by omega) (by omega) (by omega) heZ
  omega
#print axioms Paper7EightCycle.punctured_odd_one_load

theorem unitResidual_rotate (p : Fin 8 → ℕ) (y : Fin 8 → ℝ) (s i : Fin 8) :
    unitResidual (fun j => p (j+s)) (fun j => y (j+s)) i = unitResidual p y (i+s) := by
  fin_cases s <;> fin_cases i <;> rfl
#print axioms Paper7EightCycle.unitResidual_rotate

theorem alternating_punctured_load (p : Fin 8 → ℕ)
    (ho : ∀ i : Fin 8, Odd i.val → p i = 0) (hcap : ∀ i, p i ≤ 13)
    (y : Fin 8 → ℝ) (hy : y ≠ 0) (k : Fin 8) (hz : y k = 0)
    (hr : ∀ i, i ≠ k → unitResidual p y i = 0) : (∑ i, p i) ≤ 15 := by
  obtain ⟨s,hs,hk⟩ : ∃ s : Fin 8,
      (s = 0 ∨ s = 2 ∨ s = 4 ∨ s = 6) ∧ (k = s ∨ k = 1+s) := by
    fin_cases k
    · exact ⟨0,Or.inl rfl,Or.inl rfl⟩
    · exact ⟨0,Or.inl rfl,Or.inr rfl⟩
    · exact ⟨2,Or.inr (Or.inl rfl),Or.inl rfl⟩
    · exact ⟨2,Or.inr (Or.inl rfl),Or.inr rfl⟩
    · exact ⟨4,Or.inr (Or.inr (Or.inl rfl)),Or.inl rfl⟩
    · exact ⟨4,Or.inr (Or.inr (Or.inl rfl)),Or.inr rfl⟩
    · exact ⟨6,Or.inr (Or.inr (Or.inr rfl)),Or.inl rfl⟩
    · exact ⟨6,Or.inr (Or.inr (Or.inr rfl)),Or.inr rfl⟩
  have ho' : ∀ i : Fin 8, Odd i.val → p (i+s) = 0 := by
    intro i hi
    apply ho
    rcases hs with rfl | rfl | rfl | rfl <;>
      fin_cases i <;> norm_num at hi
    all_goals norm_num
  have hy' : (fun i => y (i+s)) ≠ 0 := by
    intro hh
    apply hy
    funext i
    have he := congrFun hh (i-s)
    simpa only [sub_add_cancel,Pi.zero_apply] using he
  let σ : Fin 8 → Fin 8 := fun i => i+s
  have hσ : IsDihedral 8 σ := by refine ⟨s,Or.inl ?_⟩; intro i; rfl
  have hsum : (∑ i, p (i+s)) = ∑ i, p i :=
    (Paper7PruningCanonical.dihedral_bijective 8 (by decide) σ hσ).sum_comp p
  rw [← hsum]
  rcases hk with hk | hk
  · apply punctured_even_zero_load (fun i => p (i+s)) ho' (fun i => hcap (i+s))
      (fun i => y (i+s)) hy'
    · simpa only [zero_add,← hk] using hz
    · intro i hi
      rw [unitResidual_rotate]
      apply hr
      rw [hk]
      intro hh
      apply hi
      exact add_right_cancel (show i+s = 0+s by simpa using hh)
  · apply punctured_odd_one_load (fun i => p (i+s)) ho' (fun i => hcap (i+s))
      (fun i => y (i+s)) hy'
    · simpa only [← hk] using hz
    · intro i hi
      rw [unitResidual_rotate]
      apply hr
      rw [hk]
      exact fun hh => hi (add_right_cancel hh)
#print axioms Paper7EightCycle.alternating_punctured_load

end Paper7EightCycle
