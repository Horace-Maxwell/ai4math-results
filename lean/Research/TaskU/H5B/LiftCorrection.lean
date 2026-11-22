import Research.TaskU.H5B.LiftBlock

namespace TaskU.H5.Spectrum
open Finset Matrix
open Cyc5 (V)
open scoped BigOperators

def redHom : V →+* F where
  toFun := Cyc5.residue
  map_zero' := by decide
  map_one' := by decide
  map_mul' := Cyc5.residue_mul
  map_add' x y := by simp [Cyc5.add_def,Cyc5.residue,Cyc5.sumCoeff,Cyc5.add]; ring

def powers (x : V) (c : F) : ℤ := ![x.a,x.b,x.c,x.d,0] c

def centered (x : V) (c : F) : ℤ := powers x c - Cyc5.sumCoeff x / 5

theorem powers_total (x : V) : ∑ c : F, powers x c = Cyc5.sumCoeff x := by
  rw [sum_five]; simp [powers,Cyc5.sumCoeff]

theorem centered_total (x : V) (hx : redHom x = 0) : ∑ c : F, centered x c = 0 := by
  have hz : 5 ∣ Cyc5.sumCoeff x := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hx
  rw [show (∑ c : F, centered x c) = (∑ c : F, powers x c) - 5*(Cyc5.sumCoeff x/5) by
    simp [centered,Finset.sum_sub_distrib,ZMod.card]]
  rw [powers_total]
  omega

def evaluateCoeffs (p : F → ℤ) : V := ∑ c : F, (p c : V)*Cyc5.rootAt c

private theorem rootSum : ∀ j : F, (∑ b : F, Cyc5.rootAt (b*j)) = if j=0 then (5:V) else 0 := by
  decide +kernel

private theorem rootSumOne : ∑ c : F, Cyc5.rootAt c = (0:V) := by decide +kernel

private theorem eval_powers (x : V) : evaluateCoeffs (powers x) = x := by
  unfold evaluateCoeffs
  rw [sum_five]
  change Cyc5.add (Cyc5.add (Cyc5.add (Cyc5.add (Cyc5.mul (Cyc5.scalar x.a) (Cyc5.scalar 1))
    (Cyc5.mul (Cyc5.scalar x.b) Cyc5.root)) (Cyc5.mul (Cyc5.scalar x.c) ⟨0,0,1,0⟩))
    (Cyc5.mul (Cyc5.scalar x.d) ⟨0,0,0,1⟩)) (Cyc5.mul (Cyc5.scalar 0) _) = _
  ext <;> simp [Cyc5.add,Cyc5.mul,Cyc5.root,Cyc5.scalar]

theorem eval_centered (x : V) : evaluateCoeffs (centered x) = x := by
  simp only [evaluateCoeffs,centered, Int.cast_sub, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, rootSumOne, mul_zero, sub_zero]
  exact eval_powers x

def entryShift (q : ℤ) (x : V) (c : F) : ℤ :=
  (if c=0 then q else 0) + centered x c

theorem entryShift_total (q : ℤ) (x : V) (hx : redHom x=0) :
    (∑ c : F, entryShift q x c) = q := by
  simp [entryShift, Finset.sum_add_distrib, centered_total x hx]

theorem eval_entryShift (q : ℤ) (x : V) : evaluateCoeffs (entryShift q x) = (q:V)+x := by
  simp only [evaluateCoeffs,entryShift,Int.cast_add,add_mul,Finset.sum_add_distrib]
  rw [show (∑ c : F, (centered x c : V)*Cyc5.rootAt c) = x from eval_centered x]
  simp [apply_ite,ite_mul,show Cyc5.rootAt (0:F)=(1:V) from rfl]

theorem shift_block (f : H → ℤ) (p : F → F → ℤ) :
    coordBlock (fun g => f g+p g.a g.c) =
      (coordBlock f).updateCol 0 (fun i => coordBlock f i 0 + 5*evaluateCoeffs (p i)) := by
  have he (i j : F) : (∑ b : F, ∑ c : F, (p (i-j) c : V)*Cyc5.rootAt (c+b*j)) =
      (∑ b : F, Cyc5.rootAt (b*j))*evaluateCoeffs (p (i-j)) := by
    simp_rw [← Cyc5.rootAt_add]
    change (∑ b : F, ∑ c : F, (p (i-j) c : V)*(Cyc5.rootAt c * Cyc5.rootAt (b*j))) = _
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    rw [← Finset.mul_sum, mul_comm]
    rfl
  ext i j : 1
  simp only [coordBlock,Matrix.of_apply,Int.cast_add,add_mul,Finset.sum_add_distrib,he,rootSum]
  by_cases h : j=0
  · subst j; simp
  · simp [h]

end TaskU.H5.Spectrum
