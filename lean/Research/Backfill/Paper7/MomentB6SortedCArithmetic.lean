import Mathlib

/-! SOURCE ONLY. Both necessary bounds for a complete sorted-left c slice.
The original a window has ceil((A-c)/2) <= a <= min(c,A-c). Its squared
pair is increasing on that upper half, so its endpoint gives an exact maximum.
A complementary lower bound uses (a-b)^2 >= 0. No enumeration, graph premise,
changed Q interval, numerical result or resource option is introduced. -/
set_option autoImplicit false
namespace Paper7MomentCounts

theorem b6PairSquares_mono_upperHalf (s a m : ℕ)
    (ha : a ≤ s) (hhalf : s-a ≤ a) (ham : a ≤ m) (hm : m ≤ s) :
    a^2+(s-a)^2 ≤ m^2+(s-m)^2 := by
  have hna : s-m ≤ a := by omega
  have hb : s-a = (s-m)+(m-a) := by omega
  have hp := Nat.mul_le_mul_right (m-a) hna
  calc
    a^2+(s-a)^2 = a^2+((s-m)+(m-a))^2 := by rw [hb]
    _ ≤ (a+(m-a))^2+(s-m)^2 := by nlinarith
    _ = m^2+(s-m)^2 := by rw [Nat.add_sub_of_le ham]
#print axioms Paper7MomentCounts.b6PairSquares_mono_upperHalf

def b6SortedCUpper (A c : ℕ) : ℕ :=
  c^2+(min c (A-c))^2+(A-c-min c (A-c))^2
#print axioms Paper7MomentCounts.b6SortedCUpper

theorem b6LeftSquares_le_sortedCUpper (A c a : ℕ)
    (hlo : (A-c+1)/2 ≤ a) (hhi : a ≤ min c (A-c)) :
    c^2+a^2+(A-c-a)^2 ≤ b6SortedCUpper A c := by
  have ha : a ≤ A-c := le_trans hhi (min_le_right _ _)
  have hhalf : A-c-a ≤ a := by omega
  have hp := b6PairSquares_mono_upperHalf (A-c) a (min c (A-c))
    ha hhalf hhi (min_le_right _ _)
  unfold b6SortedCUpper
  omega
#print axioms Paper7MomentCounts.b6LeftSquares_le_sortedCUpper

theorem b6SortedCResidualUpper_of_leftResidual (Z R A c a : ℕ)
    (hlo : (A-c+1)/2 ≤ a) (hhi : a ≤ min c (A-c))
    (hR : R ≤ c^2+a^2+(A-c-a)^2+(Z-A)^2) :
    R ≤ b6SortedCUpper A c+(Z-A)^2 := by
  have hp := b6LeftSquares_le_sortedCUpper A c a hlo hhi
  omega
#print axioms Paper7MomentCounts.b6SortedCResidualUpper_of_leftResidual

theorem b6PairSquares_twice_lowerBound (a b : ℕ) :
    (a+b)^2 ≤ 2*(a^2+b^2) := by
  have hp : ((a : ℤ)+(b : ℤ))^2 ≤ 2*((a : ℤ)^2+(b : ℤ)^2) := by
    nlinarith [sq_nonneg ((a : ℤ)-(b : ℤ))]
  exact_mod_cast hp
#print axioms Paper7MomentCounts.b6PairSquares_twice_lowerBound

theorem b6SortedCResidualLower_of_leftSquares (R A c a : ℕ)
    (ha : a ≤ A-c) (hB : c^2+a^2+(A-c-a)^2 ≤ R) :
    2*c^2+(A-c)^2 ≤ 2*R := by
  have hs : a+(A-c-a) = A-c := by omega
  have hp := b6PairSquares_twice_lowerBound a (A-c-a)
  rw [hs] at hp
  nlinarith
#print axioms Paper7MomentCounts.b6SortedCResidualLower_of_leftSquares

theorem b6SortedCUpper_le_cResidual (A c : ℕ) :
    b6SortedCUpper A c ≤ c^2+(A-c)^2 := by
  have hm : min c (A-c) ≤ A-c := min_le_right _ _
  have hs : min c (A-c)+(A-c-min c (A-c)) = A-c := by omega
  have hp : (min c (A-c))^2+(A-c-min c (A-c))^2 ≤
      (min c (A-c)+(A-c-min c (A-c)))^2 := by
    nlinarith [Nat.zero_le ((min c (A-c))*(A-c-min c (A-c)))]
  rw [hs] at hp
  unfold b6SortedCUpper
  omega
#print axioms Paper7MomentCounts.b6SortedCUpper_le_cResidual

end Paper7MomentCounts
