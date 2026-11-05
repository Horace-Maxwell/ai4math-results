import Mathlib

/-! Source-only finite side remainders. The row identity follows from the
actual adjacency matrix and finite neighbor set, rather than a budget premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix

namespace Paper7IntroSideRemainder
open SimpleGraph Matrix

theorem three_erased_square_budget
    {V : Type} [DecidableEq V] (W : Finset V) (h : V → ℝ) (a u v : V)
    (ha : a ∈ W) (hu : u ∈ W) (hv : v ∈ W)
    (hau : a ≠ u) (hav : a ≠ v) (huv : u ≠ v)
    (hha : h a = 1) (hsum : (∑ x ∈ W, h x ^ 2) = 20)
    (huvsum : h u + h v = 5) :
    (∑ x ∈ ((W.erase a).erase u).erase v, h x ^ 2) = 2 * h u * h v - 6 := by
  have hu' : u ∈ W.erase a := Finset.mem_erase.mpr ⟨hau.symm, hu⟩
  have hv' : v ∈ (W.erase a).erase u :=
    Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_erase.mpr ⟨hav.symm, hv⟩⟩
  have h₁ := Finset.sum_erase_add W (fun x => h x ^ 2) ha
  have h₂ := Finset.sum_erase_add (W.erase a) (fun x => h x ^ 2) hu'
  have h₃ := Finset.sum_erase_add ((W.erase a).erase u) (fun x => h x ^ 2) hv'
  rw [hha, hsum] at h₁
  have hvexpr : h v = 5 - h u := by linarith only [huvsum]
  rw [hvexpr] at h₃ ⊢
  nlinarith only [h₁, h₂, h₃]
#print axioms Paper7IntroSideRemainder.three_erased_square_budget

theorem eigen_three_side_remainder_sum
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f h : V → ℝ)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (W : Finset V) (a u v d s : V)
    (hscale : ∀ x ∈ W, f x = 3 * h x)
    (hside : ∀ x, G.Adj s x → x ∈ W)
    (hd : d = u ∨ d = v) (hsd : G.Adj s d)
    (havoid : ∀ x, (x = a ∨ x = u ∨ x = v) → G.Adj s x → x = d) :
    (∑ x ∈ (((W.erase a).erase u).erase v).filter (fun x => G.Adj s x), h x) =
      f s - h d := by
  let R := ((W.erase a).erase u).erase v
  let P := R.filter (fun x => G.Adj s x)
  have hdR : d ∉ R := by
    intro hx
    have hv := (Finset.mem_erase.mp hx).1
    have hu := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    rcases hd with hdu | hdv
    · exact hu hdu
    · exact hv hdv
  have hdP : d ∉ P := fun hx => hdR (Finset.mem_filter.mp hx).1
  have hPW : P ⊆ W := by
    intro x hx
    have hr := (Finset.mem_filter.mp hx).1
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).2).2
  have hN : G.neighborFinset s = insert d P := by
    ext x
    constructor
    · intro hx
      have hsx := (G.mem_neighborFinset s x).mp hx
      by_cases hxd : x = d
      · exact Finset.mem_insert.mpr (Or.inl hxd)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        apply Finset.mem_filter.mpr
        refine ⟨?_, hsx⟩
        have hxa : x ≠ a := fun he => hxd (havoid x (Or.inl he) hsx)
        have hxu : x ≠ u := fun he => hxd (havoid x (Or.inr (Or.inl he)) hsx)
        have hxv : x ≠ v := fun he => hxd (havoid x (Or.inr (Or.inr he)) hsx)
        exact Finset.mem_erase.mpr ⟨hxv,
          Finset.mem_erase.mpr ⟨hxu, Finset.mem_erase.mpr ⟨hxa, hside x hsx⟩⟩⟩
    · intro hx
      rcases Finset.mem_insert.mp hx with hxd | hxP
      · rw [hxd]
        exact (G.mem_neighborFinset s d).mpr hsd
      · exact (G.mem_neighborFinset s x).mpr (Finset.mem_filter.mp hxP).2
  have hsum : (∑ x ∈ P, f x) = 3 * ∑ x ∈ P, h x := by
    calc
      (∑ x ∈ P, f x) = ∑ x ∈ P, 3 * h x :=
        Finset.sum_congr rfl (fun x hx => hscale x (hPW hx))
      _ = _ := (Finset.mul_sum P (fun x => h x) 3).symm
  have hrow : f d + (∑ x ∈ P, f x) = 3 * f s := by
    simpa only [G.adjMatrix_mulVec_apply, hN, Finset.sum_insert hdP,
      Pi.smul_apply, smul_eq_mul] using congrFun hAf s
  rw [hscale d (hside d hsd), hsum] at hrow
  change (∑ x ∈ P, h x) = f s - h d
  linarith only [hrow]
#print axioms Paper7IntroSideRemainder.eigen_three_side_remainder_sum

end Paper7IntroSideRemainder
