import Mathlib

/-! Source-only author candidate by Codex subagent p6_binding_spotcheck.
The public discrete Fourier equivalence diagonalizes the two-neighbour
operator on ZMod. This file does not identify it with the frozen Fin-indexed
cycle graph, convert the character values to real cosines, or count roots.
No compilation or kernel acceptance is claimed here. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Polynomial

namespace Paper7Lemma41

/-- The two-neighbour operator, before identifying its index type with a cycle. -/
def cycleZModOperator (b : ℕ) [NeZero b] :
    Module.End ℂ (ZMod b → ℂ) where
  toFun f j := f (j - 1) + f (j + 1)
  map_add' f g := by
    funext j
    change (f (j - 1) + g (j - 1)) + (f (j + 1) + g (j + 1)) =
      (f (j - 1) + f (j + 1)) + (g (j - 1) + g (j + 1))
    ring
  map_smul' c f := by
    funext j
    change c * f (j - 1) + c * f (j + 1) =
      c * (f (j - 1) + f (j + 1))
    exact (mul_add c _ _).symm
#print axioms Paper7Lemma41.cycleZModOperator

/-- Translation becomes multiplication by the corresponding additive character. -/
theorem dft_translate (b : ℕ) [NeZero b] (f : ZMod b → ℂ)
    (a k : ZMod b) :
    ZMod.dft (fun j => f (j + a)) k =
      ZMod.stdAddChar (a * k) * ZMod.dft f k := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ ?_
  intro j
  change ZMod.stdAddChar (-(j * k)) * f (j + a) =
    ZMod.stdAddChar (a * k) *
      (ZMod.stdAddChar (-((j + a) * k)) * f (j + a))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  rw [show a * k + -((j + a) * k) = -(j * k) by ring]
#print axioms Paper7Lemma41.dft_translate

/-- The Fourier transform of the actual two-neighbour operator. -/
theorem dft_cycleZModOperator_apply (b : ℕ) [NeZero b]
    (f : ZMod b → ℂ) (k : ZMod b) :
    ZMod.dft (cycleZModOperator b f) k =
      (ZMod.stdAddChar k + ZMod.stdAddChar (-k)) * ZMod.dft f k := by
  change ZMod.dft ((fun j => f (j - 1)) + (fun j => f (j + 1))) k = _
  rw [map_add]
  change ZMod.dft (fun j => f (j - 1)) k +
    ZMod.dft (fun j => f (j + 1)) k = _
  simp only [sub_eq_add_neg]
  rw [dft_translate b f (-1) k, dft_translate b f 1 k]
  simp only [neg_one_mul, one_mul]
  ring
#print axioms Paper7Lemma41.dft_cycleZModOperator_apply

/-- A full linear conjugacy, using the public Fourier linear equivalence. -/
theorem dft_conj_cycleZModOperator (b : ℕ) [NeZero b] :
    (ZMod.dft (N := b) (E := ℂ)).conj (cycleZModOperator b) =
      (Matrix.diagonal (fun k : ZMod b =>
        ZMod.stdAddChar k + ZMod.stdAddChar (-k))).toLin' := by
  apply LinearMap.ext
  intro f
  funext k
  rw [LinearEquiv.conj_apply_apply, dft_cycleZModOperator_apply,
    Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rw [LinearEquiv.apply_symm_apply]
#print axioms Paper7Lemma41.dft_conj_cycleZModOperator

/-- Characteristic polynomial with every Fourier frequency retained. -/
theorem cycleZModOperator_charpoly (b : ℕ) [NeZero b] :
    (cycleZModOperator b).charpoly =
      ∏ k : ZMod b, (X - C (ZMod.stdAddChar k + ZMod.stdAddChar (-k))) := by
  rw [← LinearEquiv.charpoly_conj
    (ZMod.dft (N := b) (E := ℂ)) (cycleZModOperator b)]
  rw [dft_conj_cycleZModOperator, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]
#print axioms Paper7Lemma41.cycleZModOperator_charpoly

end Paper7Lemma41
