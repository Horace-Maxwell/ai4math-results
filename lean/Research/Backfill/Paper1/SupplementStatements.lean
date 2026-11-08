import Research.Backfill.Paper1.Challenge

/-!
Task D candidate supplements. Each definition states an acceptance obligation;
none is a theorem or an assumption supplied to a final mathematical result.
The old v2 and its acceptance records remain immutable. See SCOPE.md.
-/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper1.NarrowSupplement
open Challenge Finset

/-- The real part of the genuine finite Ramanujan sum. -/
def ramanujanReal (m u : ℕ) : ℝ :=
  ∑ l ∈ range m, if Nat.Coprime l m then
    Real.cos (2 * Real.pi * ((l * u : ℕ) : ℝ) / (m : ℝ)) else 0

/-- T:229–231: genuine prime-power Ramanujan entries, not just a polynomial alias. -/
def RamanujanEntry : Prop :=
  ∀ p k i j : ℕ, p.Prime → 1 ≤ k → i ≤ k → j ≤ k →
    tEntry k p i j = (Nat.totient (p ^ (k - i)) : ℝ) *
      ramanujanReal (p ^ (k - j)) (p ^ i)

/-- T:224,232: symmetry and all row sums. -/
def TransformRows : Prop :=
  ∀ x : ℝ, 1 < x → ∀ k : ℕ, 1 ≤ k →
    (∀ i ≤ k, ∀ j ≤ k, tEntry k x i j = tEntry k x j i) ∧
    (∀ i ≤ k, tMulVec k x (fun _ => 1) i = if i = k then x ^ k else 0)

/-- T:253–254: linearity for every path coordinate in the full integer range. -/
def PathLinear : Prop :=
  ∀ x : ℝ, 1 < x → ∀ k : ℕ, 1 ≤ k → ∀ j : ℤ, -1 ≤ j → j ≤ (k : ℤ) - 1 →
    ∀ r s : ℝ, ∀ v w : ℕ → ℝ,
      z x k (fun i => r * v i + s * w i) j = r * z x k v j + s * z x k w j

/-- T:253: a convex combination of precisely the permitted tail coordinates. -/
def PathConvex : Prop :=
  ∀ x : ℝ, 1 < x → ∀ k : ℕ, 1 ≤ k → ∀ j : ℤ, -1 ≤ j → j ≤ (k : ℤ) - 1 →
    ∃ c : ℕ → ℝ,
      (∀ i ∈ Icc (j + 1).toNat k, 0 ≤ c i) ∧
      (∑ i ∈ Icc (j + 1).toNat k, c i) = 1 ∧
      ∀ w : ℕ → ℝ, z x k w j = ∑ i ∈ Icc (j + 1).toNat k, c i * w i

/-- T:263–270: row/path identities, including the last row. -/
def PathCoordinates : Prop :=
  ∀ x : ℝ, 1 < x → ∀ k : ℕ, 1 ≤ k → ∀ w : ℕ → ℝ,
    tMulVec k x w k = x ^ k * z x k w (-1) ∧
    ∀ u < k, tMulVec k x w u = x ^ (k - 1) * (x - 1) *
      (z x k w ((k : ℤ) - 1 - u) - w (k - 1 - u))

/-- T:274–276,792–795: all integer lower bounds and the two initial values. -/
def MuBounds : Prop :=
  ∀ x : ℝ, 2 < x →
    (∀ j : ℤ, -1 ≤ j → (x - 2) / x ≤ mu x j ∧ mu x j ≤ 1) ∧
    (∀ j : ℕ, mu x 0 ≤ mu x j ∧ mu x j ≤ mu x 1) ∧
    mu x 0 = (x - 2) / x ∧ mu x 1 = ((x - 1) ^ 2 + 1) / x ^ 2

/-- T:585–592: the exact fixed-point formula and both strict parity sides. -/
def MuClosedParity : Prop :=
  ∀ x : ℝ, 2 < x → ∀ j : ℕ,
    mu x j - muInf x = (-1 / x) ^ (j + 1) * (1 - muInf x) ∧
    (Odd j → muInf x < mu x j) ∧ (Even j → mu x j < muInf x)

/-- M3, T:312: the full integer-index alternating-path identity. -/
def AlternatingPath : Prop :=
  ∀ x : ℝ, 2 < x → ∀ k : ℕ, 1 ≤ k → ∀ j : ℤ, -1 ≤ j → j ≤ (k : ℤ) - 1 →
    |z x k sAlt j| = mu x ((k : ℤ) - 2 - j)

/-- M2, T:450: the complete norm/corner identity for arbitrary matrices. -/
def GeneralGNorm : Prop :=
  ∀ a b : ℕ, ∀ p q : ℝ, ∀ Y : ℕ → ℕ → ℝ,
    Gval a b p q Y = l1Mat a b (triple a b p q Y) -
      2 * negPt (triple a b p q Y a b)

/-- M2, T:448–450: genuine simple-graph energy, all legal D including empty. -/
def GeneralEqG : Prop :=
  ∀ p q a b : ℕ, p.Prime → q.Prime → p ≠ q → 1 ≤ a → 1 ≤ b →
    ∀ D : Finset ℕ, D ⊆ (p ^ a * q ^ b).properDivisors →
      2 * energy (p ^ a * q ^ b) D = ((p ^ a * q ^ b : ℕ) : ℝ) +
        Gval a b p q (fun i j => 2 * divMat p q D i j - 1)

/-- T:814–830: every row formula and the complete last row. -/
def MatrixFacts : Prop :=
  ∀ p : ℝ, 2 < p → ∀ a : ℕ, 2 ≤ a →
    (∀ i < a,
      tEntry a p i a = p ^ (a - 1 - i) * (p - 1) ∧
      rowAbsSum a p i = 2 * p ^ (a - 1) * (p - 1) ∧
      tMulVec a p sAlt i = (-1 : ℝ) ^ (a - i) * p ^ (a - 1) * (p - 1) *
        (1 + mu p ((i : ℤ) - 1))) ∧
    tEntry a p a a = 1 ∧ rowAbsSum a p a = p ^ a ∧
    (∀ j < a, tEntry a p a j = p ^ (a - 1 - j) * (p - 1))

/-- T:817,831–834: all bounds use only the original real regions. -/
def MatrixBounds : Prop :=
  ∀ a : ℕ, 2 ≤ a → ∀ p q : ℝ, Regions p q →
    (∀ ζ : ℕ → ℝ, (∀ i ≤ a, |ζ i| ≤ 1) →
      ∀ i ≤ a, |tMulVec a p ζ i| ≤ rowAbsSum a p i) ∧
    (∀ i < a, 2 * tEntry a p i a ≤ |tMulVec a p sAlt i|) ∧
    p ^ (a - 1) * (p - 2) ≤ deltaK a p ∧ 3 ≤ deltaK a p ∧
    p ^ a < (q - 1) * deltaK a p ∧
    (∀ i ≤ a, rowAbsSum a p i ≤ (q - 1) * |tMulVec a p sAlt i|)

/-- T:579–583,799–805: exact cell cases with their original signs and thresholds. -/
def CellValues : Prop :=
  ∀ P μ A B : ℝ, 2 ≤ P → 0 ≤ μ → μ ≤ 1 →
    hcell P μ (-A) (-B) = hcell P μ A B ∧
    hcell P μ 0 B = 2 * μ * |B| ∧
    (0 < A * B → |B| ≤ |A| → hcell P μ A B = -2 * (P - μ) * |B|) ∧
    (A * B ≤ 0 → |B| ≤ P * |A| → hcell P μ A B = 0) ∧
    (0 < A * B → |A| ≤ |B| → hcell P μ A B = 2 * (μ * |B| - P * |A|)) ∧
    (A * B ≤ 0 → P * |A| ≤ |B| → hcell P μ A B = 2 * μ * (|B| - P * |A|))

/-- T:806–812: strictness and the explicitly stated zero boundary. -/
def CellStrictBoundary : Prop :=
  (∀ P μ A B : ℝ, 2 ≤ P → 0 ≤ μ → μ ≤ 1 →
    0 < A * B → |B| < P * |A| → hcell P μ A B < 0) ∧
  (∀ P μ A : ℝ, 2 ≤ P → 0 < μ → μ ≤ 1 → 0 < A →
    hcell P μ A (P * A / μ) = 0)

/-- T:564–568,778–797: prime admissibility and the real parameter consequences. -/
def ParameterRegions : Prop :=
  (∀ p q : ℕ, DistinctOddPrimes p q → Regions p q ∧ ParamXR q ((p : ℝ) - 1)) ∧
  (∀ x R : ℝ, ParamXR x R → R + 1 < (x - 1) * (R - 1)) ∧
  (∀ p q : ℝ, Regions p q →
    ((4 ≤ p - 1 ∧ 2 ≤ q - 1) ∨ (p - 1 = 2 ∧ 4 ≤ q - 1)) ∧
      2 ≤ q - 1 ∧ 8 ≤ (p - 1) * (q - 1))

/-- The literal product-of-divisor-sets convention on the legal domain (Remark 16). -/
def MultiplicativeBridge : Prop :=
  ∀ p q a b : ℕ, p.Prime → q.Prime → p ≠ q → 1 ≤ a → 1 ≤ b →
    ∀ D : Finset ℕ, IsConnSet (p ^ a * q ^ b) D →
      (IsMultSet p q a b D ↔ ∃ A B : Finset ℕ,
        A ⊆ (p ^ a).divisors ∧ B ⊆ (q ^ b).divisors ∧
          D = (A ×ˢ B).image (fun ij => ij.1 * ij.2))

/-- Only the stated two-prime legal domain, no general-n Le–Sander theorem. -/
def MultiplicativeMaxComparison : Prop :=
  ∀ p q a b : ℕ, DistinctOddPrimes p q → 1 ≤ a → 1 ≤ b →
    ∀ V W : ℝ, ∀ S : Set (Finset ℕ),
      MaxEnergy (p ^ a * q ^ b) V S → MultMaxEnergy p q a b W → W ≤ V

def disjointCliques (p q : ℕ) : SimpleGraph (Fin p × Fin q) :=
  SimpleGraph.fromRel (fun u v => u.1 = v.1)

def completeParts (p q : ℕ) : SimpleGraph (Fin p × Fin q) :=
  SimpleGraph.fromRel (fun u v => u.2 ≠ v.2)

def unitaryProduct (p q : ℕ) : SimpleGraph (Fin p × Fin q) :=
  SimpleGraph.fromRel (fun u v => u.1 ≠ v.1 ∧ u.2 ≠ v.2)

/-- T:531–538: genuine graph isomorphisms; universal p,q also gives the swapped statements. -/
def PQGraphModels : Prop :=
  ∀ p q : ℕ, DistinctOddPrimes p q →
    Nonempty ((icg (p * q) {1}) ≃g unitaryProduct p q) ∧
    Nonempty ((icg (p * q) {p}) ≃g disjointCliques p q) ∧
    Nonempty ((icg (p * q) {1, p}) ≃g completeParts p q) ∧
    icg (p * q) {1, p, q} = ⊤

/-- T:550–558: the retained worked example, including its path and intermediate values. -/
def NearExampleDetails : Prop :=
  z 3 2 g2 1 = -1 ∧ z 3 2 g2 0 = 1 / 3 ∧ z 3 2 g2 (-1) = 7 / 9 ∧
  NA 2 g2 = {0} ∧ l1 2 (tMulVec 2 3 g2) = 23 ∧
  ∀ p : ℝ, 5 ≤ p →
    Gval 2 2 p 3 (fun i j => sAlt i * g2 j) = 23 * dNorm 2 p ∧
    0 < triple 2 2 p 3 (fun i j => sAlt i * g2 j) 2 2

/-- Abstract/Introduction: every positive exponent pair with min≤2, both parities. -/
def CompleteMinTwo : Prop :=
  ∀ p q a b : ℕ, DistinctOddPrimes p q → 1 ≤ a → 1 ≤ b → min a b ≤ 2 →
    if Even (a + b) then
      MaxEnergy (p ^ a * q ^ b)
        ((((p ^ a * q ^ b : ℕ) : ℝ) + dClosed a p * dClosed b q) / 2 -
          deltaK a p * deltaK b q)
        {oddSet p q a b, (evenSet p q a b).erase (p ^ a * q ^ b)}
    else
      MaxEnergy (p ^ a * q ^ b)
        ((((p ^ a * q ^ b : ℕ) : ℝ) + dClosed a p * dClosed b q) / 2)
        {evenSet p q a b}

end BackfillPaper1.NarrowSupplement
