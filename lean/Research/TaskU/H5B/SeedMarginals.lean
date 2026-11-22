import Research.TaskU.H5B.Seeds
import Research.TaskU.H5.Divisibility
import Research.TaskU.H5.Cyc5

namespace TaskU.H5.Spectrum
open Finset
open scoped BigOperators

def marginal (f : H → ℤ) (a b : F) : ℤ := ∑ c : F, f ⟨a,b,c⟩
def lineCount (P : F → F → ℤ) (u v r : F) : ℤ :=
  ∑ a : F, ∑ b : F, if u*a+v*b=r then P a b else 0

theorem marginal_aug (f : H → ℤ) : aug f = abAug (marginal f) := by
  exact sumH f

theorem marginal_ray (f : H → ℤ) (u v : F) : ray f u v = abRay (marginal f) u v := by
  unfold ray abRay
  congr 1
  funext r
  rw [counts,sumH]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases he : u*a+v*b=r <;> simp [he, marginal]

def wseed (s : Fin 5) (a b : F) := seed s b a
def baseRay (s : Fin 5) := abRay (wseed s) 1 0

theorem swapped_data : ∀ s : Fin 5,
    abAug (wseed s)=5*seedA s ∧ Cyc5.norm (baseRay s)=5 ∧
    (∏ j : F, Cyc5.norm (abRay (wseed s) j 1))=15625 := by decide +kernel

theorem add_rows (P : F → F → ℤ) (q : F → ℤ) :
    abAug (fun a b => P a b + q a) = abAug P + 5*(∑ a, q a) := by
  simp only [abAug, sum_add_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, ← mul_sum]
  rfl

theorem count_rows (P : F → F → ℤ) (q : F → ℤ) (j r : F) :
    lineCount (fun a b => P a b + q a) j 1 r = lineCount P j 1 r + ∑ a, q a := by
  unfold lineCount
  simp_rw [one_mul, ite_add_zero, sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro a _
  have he (b : F) : j*a+b=r ↔ b=r-j*a := by constructor <;> intro h <;> linear_combination h
  simp [he]

theorem ordinary_rows (P : F → F → ℤ) (q : F → ℤ) (j : F) :
    abRay (fun a b => P a b + q a) j 1 = abRay P j 1 := by
  change profile (lineCount _ _ _) = profile (lineCount _ _ _)
  ext <;> simp [profile, count_rows]

theorem horizontal_rows (P : F → F → ℤ) (q : F → ℤ) :
    abRay (fun a b => P a b + q a) 1 0 =
    Cyc5.add (abRay P 1 0) (Cyc5.mul (Cyc5.scalar 5) (profile q)) := by
  have count_h (r : F) : lineCount (fun a b => P a b + q a) 1 0 r =
      lineCount P 1 0 r + 5*q r := by
    simp only [lineCount, one_mul,zero_mul,add_zero,ite_add_zero,sum_add_distrib]
    simp [ZMod.card]
  change profile (lineCount _ _ _) = Cyc5.add (profile (lineCount _ _ _)) _
  ext <;> simp [profile, count_h,Cyc5.add,Cyc5.mul,Cyc5.scalar] <;> ring

end TaskU.H5.Spectrum
