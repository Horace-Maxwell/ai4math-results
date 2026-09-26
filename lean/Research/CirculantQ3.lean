import Mathlib

/-! Exact arithmetic core of the q=3 case of Roldán arXiv:2604.09491,
Conjecture 1.3. The graph/Fourier spectral bridge is NOT formalized here.
The parameter x below is p-5. Each bit encodes a proper-divisor exponent pair.
No external certificate is trusted: finite inequalities use kernel decide,
and the coefficient table is proved equal to explicit Ramanujan tables. -/
namespace CirculantQ3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def basisCoeff : Fin 12 → Fin 11 → Fin 3 → ℤ :=
  ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![360, 162, 18], ![-360, -162, -18], ![0, 0, 0], ![0, 0, 0], ![-360, -162, -18]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![360, 162, 18], ![-240, -108, -12], ![-120, -54, -6], ![0, 0, 0], ![-360, -162, -18], ![240, 108, 12]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![360, 162, 18], ![-240, -108, -12], ![-80, -36, -4], ![-40, -18, -2], ![-360, -162, -18], ![240, 108, 12], ![80, 36, 4]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-360, -162, -18], ![-120, -54, -6], ![-40, -18, -2], ![-20, -9, -1], ![360, 162, 18], ![120, 54, 6], ![40, 18, 2]], ![![0, 0, 0], ![0, 0, 0], ![360, 162, 18], ![-360, -162, -18], ![0, 0, 0], ![0, 0, 0], ![-288, -144, -18], ![288, 144, 18], ![0, 0, 0], ![0, 0, 0], ![-72, -18, 0]], ![![0, 0, 0], ![360, 162, 18], ![-240, -108, -12], ![-120, -54, -6], ![0, 0, 0], ![-288, -144, -18], ![192, 96, 12], ![96, 48, 6], ![0, 0, 0], ![-72, -18, 0], ![48, 12, 0]], ![![360, 162, 18], ![-240, -108, -12], ![-80, -36, -4], ![-40, -18, -2], ![-288, -144, -18], ![192, 96, 12], ![64, 32, 4], ![32, 16, 2], ![-72, -18, 0], ![48, 12, 0], ![16, 4, 0]], ![![-360, -162, -18], ![-120, -54, -6], ![-40, -18, -2], ![-20, -9, -1], ![288, 144, 18], ![96, 48, 6], ![32, 16, 2], ![16, 8, 1], ![72, 18, 0], ![24, 6, 0], ![8, 2, 0]], ![![0, 0, 0], ![0, 0, 0], ![-360, -162, -18], ![360, 162, 18], ![0, 0, 0], ![0, 0, 0], ![-72, -18, 0], ![72, 18, 0], ![0, 0, 0], ![0, 0, 0], ![-18, 0, 0]], ![![0, 0, 0], ![-360, -162, -18], ![240, 108, 12], ![120, 54, 6], ![0, 0, 0], ![-72, -18, 0], ![48, 12, 0], ![24, 6, 0], ![0, 0, 0], ![-18, 0, 0], ![12, 0, 0]], ![![-360, -162, -18], ![240, 108, 12], ![80, 36, 4], ![40, 18, 2], ![-72, -18, 0], ![48, 12, 0], ![16, 4, 0], ![8, 2, 0], ![-18, 0, 0], ![12, 0, 0], ![4, 0, 0]], ![![360, 162, 18], ![120, 54, 6], ![40, 18, 2], ![20, 9, 1], ![72, 18, 0], ![24, 6, 0], ![8, 2, 0], ![4, 1, 0], ![18, 0, 0], ![6, 0, 0], ![2, 0, 0]]]

def chosen (mask : Fin 2048) (j : Fin 11) : Bool := mask.val.testBit j.val

def coeff (mask : Fin 2048) (r : Fin 12) (k : Fin 3) : ℤ :=
  ∑ j : Fin 11, if chosen mask j then basisCoeff r j k else 0

def upper (mask : Fin 2048) (k : Fin 3) : ℤ :=
  ∑ r : Fin 12, |coeff mask r k|

def poly (c : Fin 3 → ℤ) (x : ℤ) : ℤ := c 0 + c 1*x + c 2*x^2

def energy (x : ℤ) (mask : Fin 2048) : ℤ :=
  ∑ r : Fin 12, |poly (coeff mask r) x|

def star : Fin 2048 := 1445

 theorem coefficient_certificate : ∀ mask : Fin 2048, mask ≠ star →
    upper mask 0 ≤ 4424 ∧ upper mask 1 ≤ 2064 ∧ upper mask 2 ≤ 242 := by
  decide +kernel

 theorem star_upper : upper star 0 = 4832 ∧ upper star 1 = 2256 ∧
    upper star 2 = 266 := by decide +kernel

 theorem star_same_sign : ∀ r : Fin 12,
    (∀ k : Fin 3, 0 ≤ coeff star r k) ∨ (∀ k : Fin 3, coeff star r k ≤ 0) := by
  decide +kernel

 theorem poly_abs_le (c : Fin 3 → ℤ) (x : ℤ) (hx : 0 ≤ x) :
    |poly c x| ≤ |c 0| + |c 1| * x + |c 2| * x^2 := by
  unfold poly
  have h1 := abs_add_le (c 0 + c 1*x) (c 2*x^2)
  have h2 := abs_add_le (c 0) (c 1*x)
  rw [abs_mul, abs_of_nonneg hx] at h2
  rw [abs_mul (c 2), abs_of_nonneg (sq_nonneg x)] at h1
  linarith

 theorem poly_abs_eq (c : Fin 3 → ℤ) (x : ℤ) (hx : 0 ≤ x)
    (hc : (∀ k, 0 ≤ c k) ∨ (∀ k, c k ≤ 0)) :
    |poly c x| = |c 0| + |c 1| * x + |c 2| * x^2 := by
  rcases hc with hc | hc
  · have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
    rw [abs_of_nonneg (show 0 ≤ poly c x by unfold poly; positivity),
      abs_of_nonneg h0, abs_of_nonneg h1, abs_of_nonneg h2]
    rfl
  · have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
    have hpoly : poly c x ≤ 0 := by
      unfold poly
      have hh1 := mul_nonpos_of_nonpos_of_nonneg h1 hx
      have hh2 := mul_nonpos_of_nonpos_of_nonneg h2 (sq_nonneg x)
      omega
    rw [abs_of_nonpos hpoly, abs_of_nonpos h0, abs_of_nonpos h1, abs_of_nonpos h2]
    unfold poly
    ring

 theorem energy_le (x : ℤ) (hx : 0 ≤ x) (mask : Fin 2048) :
    energy x mask ≤ upper mask 0 + upper mask 1*x + upper mask 2*x^2 := by
  unfold energy upper
  calc
    _ ≤ ∑ r : Fin 12, (|coeff mask r 0| + |coeff mask r 1| * x + |coeff mask r 2| * x^2) :=
      Finset.sum_le_sum fun r _ => poly_abs_le _ _ hx
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_mul]

 theorem energy_star (x : ℤ) (hx : 0 ≤ x) :
    energy x star = 4832 + 2256*x + 266*x^2 := by
  have hs : energy x star = upper star 0 + upper star 1*x + upper star 2*x^2 := by
    unfold energy upper
    simp_rw [poly_abs_eq _ _ hx (star_same_sign _)]
    simp only [Finset.sum_add_distrib, Finset.sum_mul]
  rw [hs, star_upper.1, star_upper.2.1, star_upper.2.2]

 theorem unique_maximum (x : ℤ) (hx : 0 ≤ x) (mask : Fin 2048) (hm : mask ≠ star) :
    energy x mask + 408 + 192*x + 24*x^2 ≤ energy x star := by
  have h := energy_le x hx mask
  obtain ⟨h0,h1,h2⟩ := coefficient_certificate mask hm
  have hh1 := mul_le_mul_of_nonneg_right h1 hx
  have hh2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg x)
  rw [energy_star x hx]
  linarith

 theorem strictly_smaller (x : ℤ) (hx : 0 ≤ x) (mask : Fin 2048) (hm : mask ≠ star) :
    energy x mask < energy x star := by
  have h := unique_maximum x hx mask hm
  have h1 : 0 ≤ 192*x := by positivity
  have h2 : 0 ≤ 24*x^2 := by positivity
  omega


-- Weighted Ramanujan matrices, specialized at q=3, directly from equations (8),(9).
def weightedP (p : ℤ) (a c : ℕ) : ℤ :=
  match a,c with
  | 0,0 => 0
  | 0,1 => -p*(p-1)
  | 0,2 => p*(p-1)
  | 1,0 => -p*(p-1)
  | 1,1 => (p-1)^2
  | 1,2 => p-1
  | 2,0 => p*(p-1)
  | 2,1 => p-1
  | 2,2 => 1
  | _,_ => 0

def weightedQ (b d : ℕ) : ℤ :=
  match b,d with
  | 0,0 => 0 | 0,1 => 0 | 0,2 => -18 | 0,3 => 18
  | 1,0 => 0 | 1,1 => -18 | 1,2 => 12 | 1,3 => 6
  | 2,0 => -18 | 2,1 => 12 | 2,2 => 4 | 2,3 => 2
  | 3,0 => 18 | 3,1 => 6 | 3,2 => 2 | 3,3 => 1
  | _,_ => 0

def weightedBasis (p : ℤ) (r : Fin 12) (j : Fin 11) : ℤ :=
  weightedP p (r.val / 4) (j.val / 4) * weightedQ (r.val % 4) (j.val % 4)

theorem basis_expand (x : ℤ) (r : Fin 12) (j : Fin 11) :
    weightedBasis (x+5) r j = poly (basisCoeff r j) x := by
  fin_cases r <;> fin_cases j <;>
    norm_num [weightedBasis, weightedP, weightedQ, poly, basisCoeff, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring

def weightedEigenvalue (p : ℤ) (mask : Fin 2048) (r : Fin 12) : ℤ :=
  ∑ j : Fin 11, if chosen mask j then weightedBasis p r j else 0

def exactEnergy (p : ℤ) (mask : Fin 2048) : ℤ :=
  ∑ r : Fin 12, |weightedEigenvalue p mask r|

theorem weightedEigenvalue_expand (x : ℤ) (mask : Fin 2048) (r : Fin 12) :
    weightedEigenvalue (x+5) mask r = poly (coeff mask r) x := by
  unfold weightedEigenvalue
  simp_rw [basis_expand]
  have h : ∀ j : Fin 11,
      (if chosen mask j then poly (basisCoeff r j) x else 0) =
      (if chosen mask j then basisCoeff r j 0 else 0) +
      (if chosen mask j then basisCoeff r j 1 else 0)*x +
      (if chosen mask j then basisCoeff r j 2 else 0)*x^2 := by
    intro j
    split <;> simp_all [poly]
  simp_rw [h]
  simp only [Finset.sum_add_distrib, Finset.sum_mul, poly, coeff]

theorem exactEnergy_eq_energy (x : ℤ) (mask : Fin 2048) :
    exactEnergy (x+5) mask = energy x mask := by
  unfold exactEnergy energy
  simp_rw [weightedEigenvalue_expand]


 theorem exactEnergy_unique (p : ℤ) (hp : 5 ≤ p) (mask : Fin 2048) (hm : mask ≠ star) :
    exactEnergy p mask + 24*(p^2-2*p+2) ≤ exactEnergy p star := by
  have hx : 0 ≤ p-5 := by omega
  have h := unique_maximum (p-5) hx mask hm
  have hmEq := exactEnergy_eq_energy (p-5) mask
  have hsEq := exactEnergy_eq_energy (p-5) star
  have heq : p-5+5=p := by ring
  rw [heq] at hmEq hsEq
  rw [← hmEq, ← hsEq] at h
  convert h using 1 <;> ring

 theorem exactEnergy_strict (p : ℤ) (hp : 5 ≤ p) (mask : Fin 2048) (hm : mask ≠ star) :
    exactEnergy p mask < exactEnergy p star := by
  have h := exactEnergy_unique p hp mask hm
  have hpos : 0 < 24*(p^2-2*p+2) := by nlinarith [sq_nonneg (p-1)]
  omega

 theorem exactEnergy_star (p : ℤ) (hp : 5 ≤ p) :
    exactEnergy p star = 266*p^2-404*p+202 := by
  have hx : 0 ≤ p-5 := by omega
  have h := energy_star (p-5) hx
  have hs := exactEnergy_eq_energy (p-5) star
  have heq : p-5+5=p := by ring
  rw [heq] at hs
  rw [← hs] at h
  rw [h]
  ring

#print axioms coefficient_certificate
#print axioms exactEnergy_eq_energy
#print axioms exactEnergy_unique
#print axioms exactEnergy_strict
#print axioms exactEnergy_star
end CirculantQ3
