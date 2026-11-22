import Research.TaskU.H5B.LiftColumns
import Research.TaskU.H5B.LiftCorrection

namespace TaskU.H5.Spectrum
open Finset Matrix
open Cyc5 (V)
open scoped BigOperators

def unitRepresentative (r : F) : V :=
  let φ : V := ⟨0,0,-1,-1⟩
  ![1,1,φ^3,φ,φ^2] r

private theorem representatives : ∀ r : F, r ≠ 0 →
    redHom (unitRepresentative r) = r ∧ Cyc5.norm (unitRepresentative r) = 1 := by decide +kernel

theorem lift_shift (s : Fin 5) (q : F → ℤ) :
    ∃ f : H → ℤ, (∀ a b, ∑ c : F, f ⟨a,b,c⟩ = seed s b a + q a) ∧
      Cyc5.norm (TraceWords.nonlinear f) = if (∑ a, (q a : F)) = 0 then 3125 else 625 := by
  let M := coordBlock (baseLift s)
  let r : F := ∑ a, (q a : F)
  let target : V := if r=0 then Cyc5.pi else unitRepresentative r
  have ht : redHom target = r := by
    by_cases h : r=0
    · simp only [target,h,ite_true]; decide
    · simp [target,h,(representatives r h).1]
  let w : V := ∑ i, (q i:V)*minorWeight s i
  have hw : redHom w = r := by
    simp only [w, map_sum, map_mul, map_intCast]
    change (∑ i : F, (q i:F)*(Cyc5.sumCoeff (minorWeight s i):F)) = r
    simp only [minorResidue,mul_one,r]
  let x : F → V := fun i => (target-w)*liftDir s i
  have hx (i : F) : redHom (x i) = 0 := by simp [x,ht,hw]
  let p : F → F → ℤ := fun a => entryShift (q a) (x a)
  let f : H → ℤ := fun g => baseLift s g + p g.a g.c
  refine ⟨f, ?_, ?_⟩
  · intro a b
    simp only [f,Finset.sum_add_distrib,baseAug,p,entryShift_total _ _ (hx a)]
  have hdot : (∑ i : F, x i*minorWeight s i) = target-w := by
    simp only [x,mul_assoc, ← Finset.mul_sum]
    rw [show (∑ i : F, liftDir s i * minorWeight s i)=1 by
      simpa only [_root_.mul_comm] using minorDir s, mul_one]
  have hfirst : ∑ i : F, M i 0 * minorWeight s i = 0 := by
    rw [← det_first_column]
    have hsame : M.updateCol 0 (fun i => M i 0) = M := by
      ext i j : 1
      by_cases h : j=0 <;> simp [h]
    rw [hsame,baseBlock_det]
  have hblock : (coordBlock f).det = (5:V)*target := by
    rw [show coordBlock f = M.updateCol 0 (fun i => M i 0 + 5*evaluateCoeffs (p i)) from
      shift_block _ _, det_first_column]
    simp only [p, eval_entryShift, add_mul, Finset.sum_add_distrib, hfirst, zero_add,
      mul_add, mul_assoc, ← Finset.mul_sum, hdot]
    change 5*w + 5*(target-w) = _
    ring
  rw [← norm_coordBlock,hblock, Cyc5.mul_def,Cyc5.norm_mul,show Cyc5.norm (5:V)=625 by decide]
  change _ = if r=0 then _ else _
  by_cases h : r=0
  · simp [target,h,Cyc5.norm_pi]
  · simp [target,h,(representatives r h).2]

end TaskU.H5.Spectrum
