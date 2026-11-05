import Research.Backfill.Paper7.IntroGraphRealRootObstruction

/-! Small symbolic polynomial identities for multiplicities derived from the
actual spectrum. No enumeration or externally supplied coefficient table. -/
set_option autoImplicit false
noncomputable section

namespace Paper7IntroOddMultiplicity
open Polynomial Paper7IntroOddForest

def pairedEvenFactor (u v : ℕ) : Polynomial ℤ :=
  (X ^ 2 - 1) ^ u * (X ^ 2 - 4) ^ v
#print axioms Paper7IntroOddMultiplicity.pairedEvenFactor

def radiusThreeCore : Polynomial ℤ := (X - 3) * (X - 1) ^ 3 * (X + 2) ^ 3
#print axioms Paper7IntroOddMultiplicity.radiusThreeCore

def radiusThreeCharacteristic (a u v : ℕ) : Polynomial ℤ :=
  X ^ a * pairedEvenFactor u v * radiusThreeCore
#print axioms Paper7IntroOddMultiplicity.radiusThreeCharacteristic

def radiusFourCore : Polynomial ℤ := (X - 4) * (X + 3) ^ 2 * (X + 2) * (X - 1) ^ 4
#print axioms Paper7IntroOddMultiplicity.radiusFourCore

def radiusFourCharacteristic : Polynomial ℤ := X ^ 13 * radiusFourCore
#print axioms Paper7IntroOddMultiplicity.radiusFourCharacteristic

def radiusFourForestFactor : Polynomial ℤ := X ^ 4 + 30 * X ^ 2 - 111
#print axioms Paper7IntroOddMultiplicity.radiusFourForestFactor

theorem pairedEvenFactor_comp_neg (u v : ℕ) :
    (pairedEvenFactor u v).comp (-X) = pairedEvenFactor u v := by
  simp [pairedEvenFactor]
#print axioms Paper7IntroOddMultiplicity.pairedEvenFactor_comp_neg

theorem neg_X_pow (a : ℕ) : (-X : Polynomial ℤ) ^ a = C ((-1 : ℤ) ^ a) * X ^ a := by
  have h : (-X : Polynomial ℤ) = C (-1) * X := by simp
  rw [h, mul_pow, ← Polynomial.C_pow]
#print axioms Paper7IntroOddMultiplicity.neg_X_pow

theorem radiusThreeCore_even_part :
    radiusThreeCore + radiusThreeCore.comp (-X) = -4 * radiusThreeForestFactor := by
  simp only [radiusThreeCore, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.sub_comp, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.ofNat_comp, Polynomial.one_comp]
  unfold radiusThreeForestFactor
  ring
#print axioms Paper7IntroOddMultiplicity.radiusThreeCore_even_part

theorem radiusFourCore_odd_part :
    radiusFourCore - radiusFourCore.comp (-X) = -4 * X * radiusFourForestFactor := by
  simp only [radiusFourCore, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.sub_comp, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.ofNat_comp, Polynomial.one_comp]
  unfold radiusFourForestFactor
  ring
#print axioms Paper7IntroOddMultiplicity.radiusFourCore_odd_part

theorem radiusThree_sign_product (a u v : ℕ) :
    (C ((-1 : ℤ) ^ (a + 2 * u + 2 * v + 7)) : Polynomial ℤ) *
      C ((-1 : ℤ) ^ a) = -1 := by
  have he : a + 2 * u + 2 * v + 7 + a = 2 * (a + u + v + 3) + 1 := by omega
  rw [← Polynomial.C_mul, ← pow_add, he, pow_add, pow_mul]
  norm_num
#print axioms Paper7IntroOddMultiplicity.radiusThree_sign_product

theorem radiusThreeCharacteristic_antipart (a u v : ℕ) :
    radiusThreeCharacteristic a u v - C ((-1 : ℤ) ^ (a + 2 * u + 2 * v + 7)) *
      (radiusThreeCharacteristic a u v).comp (-X) =
        -4 * (X ^ a * pairedEvenFactor u v) * radiusThreeForestFactor := by
  simp only [radiusThreeCharacteristic, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.X_comp, pairedEvenFactor_comp_neg, neg_X_pow]
  calc
    _ = X ^ a * pairedEvenFactor u v * (radiusThreeCore -
        (C ((-1 : ℤ) ^ (a + 2 * u + 2 * v + 7)) * C ((-1 : ℤ) ^ a)) *
          radiusThreeCore.comp (-X)) := by ring
    _ = _ := by
      rw [radiusThree_sign_product, neg_one_mul, sub_neg_eq_add,
        radiusThreeCore_even_part]
      ring
#print axioms Paper7IntroOddMultiplicity.radiusThreeCharacteristic_antipart

theorem radiusFourCharacteristic_antipart :
    radiusFourCharacteristic - C ((-1 : ℤ) ^ 21) *
      radiusFourCharacteristic.comp (-X) = -4 * X ^ 14 * radiusFourForestFactor := by
  have hs : (C ((-1 : ℤ) ^ 21) : Polynomial ℤ) = -1 := by norm_num
  have hx : (-X : Polynomial ℤ) ^ 13 = -X ^ 13 := by ring
  rw [hs]
  simp only [radiusFourCharacteristic, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.X_comp, hx]
  calc
    _ = X ^ 13 * (radiusFourCore - radiusFourCore.comp (-X)) := by ring
    _ = _ := by rw [radiusFourCore_odd_part]; ring
#print axioms Paper7IntroOddMultiplicity.radiusFourCharacteristic_antipart

end Paper7IntroOddMultiplicity
