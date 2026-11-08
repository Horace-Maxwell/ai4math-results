import Mathlib

/-!
Paper 1 narrow candidate, Task D (user decision 2026-11-06).
Definitions and retained target bodies derive from the immutable frozen v2.
Theorem5MinTwo replaces Theorem5; Proposition15 and Certificates are absent.
Conjecture14 is historical reference only, never an acceptance target.
See SCOPE.md, CONTRACTS.json and REVIEW status. Source only; no proof credit.
-/

set_option autoImplicit false

noncomputable section

namespace BackfillPaper1.Challenge

open Finset

/-! ## 1. Graphs, energy, sets of divisors -/

/-- The relation `gcd(u - v, n) ∈ D` on `Z/nZ = Fin n`. -/
def icgRel (n : ℕ) (D : Finset ℕ) (u v : Fin n) : Prop :=
  Nat.gcd ((u - v : Fin n) : ℕ) n ∈ D

instance (n : ℕ) (D : Finset ℕ) : DecidableRel (icgRel n D) :=
  fun u v => inferInstanceAs (Decidable (Nat.gcd ((u - v : Fin n) : ℕ) n ∈ D))

/-- The integral circulant graph `ICG_n(D)`: vertex set `Z/nZ`, distinct `u, v` adjacent iff
`gcd(u - v, n) ∈ D` (`SimpleGraph.fromRel` adds `u ≠ v` and symmetrises; the relation is
already symmetric since `gcd(v - u, n) = gcd(u - v, n)`). -/
def icg (n : ℕ) (D : Finset ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (icgRel n D)

instance (n : ℕ) (D : Finset ℕ) : DecidableRel (icg n D).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (icgRel n D)).Adj)

/-- Energy of a finite simple graph: the sum of the absolute values of the eigenvalues of its
real adjacency matrix. -/
def graphEnergy {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ :=
  ∑ i, |(G.isHermitian_adjMatrix ℝ).eigenvalues i|

/-- `E(ICG_n(D))`. -/
def energy (n : ℕ) (D : Finset ℕ) : ℝ := graphEnergy (icg n D)

/-- An admissible connection set: a nonempty set of proper divisors of `n` (Section 1). -/
def IsConnSet (n : ℕ) (D : Finset ℕ) : Prop := D.Nonempty ∧ D ⊆ n.properDivisors

/-- The maximal energy of an integral circulant graph of order `n` is `V`, and it is attained
exactly by the sets in `S`. -/
def MaxEnergy (n : ℕ) (V : ℝ) (S : Set (Finset ℕ)) : Prop :=
  (∀ D ∈ S, IsConnSet n D) ∧
    ∀ D : Finset ℕ, IsConnSet n D → energy n D ≤ V ∧ (energy n D = V ↔ D ∈ S)

/-- `{p^i q^j : 0 ≤ i ≤ a, 0 ≤ j ≤ b, i + j even}`. -/
def evenSet (p q a b : ℕ) : Finset ℕ :=
  ((range (a + 1) ×ˢ range (b + 1)).filter (fun ij => Even (ij.1 + ij.2))).image
    (fun ij => p ^ ij.1 * q ^ ij.2)

/-- `{p^i q^j : 0 ≤ i ≤ a, 0 ≤ j ≤ b, i + j odd}`. -/
def oddSet (p q a b : ℕ) : Finset ℕ :=
  ((range (a + 1) ×ˢ range (b + 1)).filter (fun ij => Odd (ij.1 + ij.2))).image
    (fun ij => p ^ ij.1 * q ^ ij.2)

/-- `p, q` are distinct odd primes. -/
def DistinctOddPrimes (p q : ℕ) : Prop := p.Prime ∧ q.Prime ∧ p ≠ q ∧ Odd p ∧ Odd q

/-! ## 2. The closed forms `d_k(x)` and `δ_k(x)` -/

/-- `d_k(x) = (2k+1) x^k + 4 ∑_{j=0}^{k-1} (-1)^{k-j} (j+1) x^j` (Theorem 1). -/
def dClosed (k : ℕ) (x : ℝ) : ℝ :=
  (2 * k + 1) * x ^ k + 4 * ∑ j ∈ range k, (-1) ^ (k - j) * ((j : ℝ) + 1) * x ^ j

/-- `δ_k(x) = (x^k (x - 1) + 2 (-1)^k) / (x + 1)` (Section 1, Remark 9). -/
def deltaK (k : ℕ) (x : ℝ) : ℝ := (x ^ k * (x - 1) + 2 * (-1) ^ k) / (x + 1)

/-! ## 3. Weighted Ramanujan transforms (Section 2) -/

/-- Entry `t_{ij}` of `T_k(x)` for `0 ≤ i, j ≤ k` (Section 2):
for `i, j < k`: `0` if `i + j ≤ k - 2`, `-x^{k-1}(x-1)` if `i + j = k - 1`,
`x^{2k-i-j-2}(x-1)^2` if `i + j ≥ k`; `t_{ik} = t_{ki} = x^{k-i-1}(x-1)` for `i < k`;
`t_{kk} = 1`. -/
def tEntry (k : ℕ) (x : ℝ) (i j : ℕ) : ℝ :=
  if i < k ∧ j < k then
    (if i + j + 2 ≤ k then 0
     else if i + j + 1 = k then -(x ^ (k - 1) * (x - 1))
     else x ^ (2 * k - i - j - 2) * (x - 1) ^ 2)
  else if i < k then x ^ (k - i - 1) * (x - 1)
  else if j < k then x ^ (k - j - 1) * (x - 1)
  else 1

/-- `(T_k(x) w)_u = ∑_{j=0}^{k} t_{uj} w_j`. -/
def tMulVec (k : ℕ) (x : ℝ) (w : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), tEntry k x u j * w j

/-- `‖v‖₁ = ∑_{u=0}^{k} |v_u|`. -/
def l1 (k : ℕ) (v : ℕ → ℝ) : ℝ := ∑ u ∈ range (k + 1), |v u|

/-- The alternating vector `s = (1, -1, 1, …)`, `s_i = (-1)^i`. -/
def sAlt (i : ℕ) : ℝ := (-1) ^ i

/-- `d_k(x) = ‖T_k(x) s_k‖₁` (Section 2). For `k = 0` it equals `1`, the paper's `d_0(x) = 1`. -/
def dNorm (k : ℕ) (x : ℝ) : ℝ := l1 k (tMulVec k x sAlt)

/-- `y ∈ {±1}^{k+1}`. -/
def IsSignVec (k : ℕ) (y : ℕ → ℝ) : Prop := ∀ i ≤ k, y i = 1 ∨ y i = -1

/-- `y = ±s_k` on the coordinates `0, …, k`. -/
def IsPmAlt (k : ℕ) (y : ℕ → ℝ) : Prop :=
  (∀ i ≤ k, y i = sAlt i) ∨ (∀ i ≤ k, y i = -sAlt i)

/-- `Y ∈ {±1}^{(a+1) × (b+1)}`. -/
def IsSignMat (a b : ℕ) (Y : ℕ → ℕ → ℝ) : Prop := ∀ i ≤ a, ∀ j ≤ b, Y i j = 1 ∨ Y i j = -1

/-- `(T_a(p) Y T_b(q)ᵀ)_{uv} = ∑_i ∑_j t^{(a,p)}_{ui} Y_{ij} t^{(b,q)}_{vj}`. -/
def triple (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) (u v : ℕ) : ℝ :=
  ∑ i ∈ range (a + 1), ∑ j ∈ range (b + 1), tEntry a p u i * Y i j * tEntry b q v j

/-- `‖Z‖₁ = ∑_{u ≤ a} ∑_{v ≤ b} |Z_{uv}|`. -/
def l1Mat (a b : ℕ) (Z : ℕ → ℕ → ℝ) : ℝ :=
  ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1), |Z u v|

/-- The divisor matrix `X` of `D`: `x_{ij} = 1` iff `p^i q^j ∈ D`. -/
def divMat (p q : ℕ) (D : Finset ℕ) (i j : ℕ) : ℝ := if p ^ i * q ^ j ∈ D then 1 else 0

/-- `Y = ε s_a s_bᵀ` on `0..a × 0..b`. -/
def IsPmCheckerboard (a b : ℕ) (Y : ℕ → ℕ → ℝ) : Prop :=
  (∀ i ≤ a, ∀ j ≤ b, Y i j = sAlt i * sAlt j) ∨ (∀ i ≤ a, ∀ j ≤ b, Y i j = -(sAlt i * sAlt j))

/-! ## 4. Path and potential (Sections 3 and 4) -/

/-- The path of Section 3 counted from the top: `zRev x k w d = z_{k-1-d}` (`0 ≤ d ≤ k`), i.e.
`z_{k-1} = w_k` and `z_{j-1} = (z_j + (x-1) w_j) / x` for `j = k-1, …, 0`. -/
def zRev (x : ℝ) (k : ℕ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => w k
  | d + 1 => (zRev x k w d + (x - 1) * w (k - 1 - d)) / x

/-- `z_j` for `-1 ≤ j ≤ k - 1` (paper's index). -/
def z (x : ℝ) (k : ℕ) (w : ℕ → ℝ) (j : ℤ) : ℝ := zRev x k w ((k : ℤ) - 1 - j).toNat

/-- `muSeq x n = μ_{n-1}`: `μ_{-1} = 1`, `μ_j = (x - 1 - μ_{j-1}) / x` (Section 4). -/
def muSeq (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (x - 1 - muSeq x n) / x

/-- The potential `μ_j`, `j ≥ -1` (paper's index). -/
def mu (x : ℝ) (j : ℤ) : ℝ := muSeq x (j + 1).toNat

/-- `c_j = (x - 1)(1 + μ_{j-1}) / x`. -/
def cc (x : ℝ) (j : ℤ) : ℝ := (x - 1) * (1 + mu x (j - 1)) / x

/-- `NA(y) = {0 ≤ j ≤ k - 1 : y_j = y_{j+1}}`. -/
def NA (k : ℕ) (y : ℕ → ℝ) : Finset ℕ := (range k).filter (fun j => y j = y (j + 1))

/-! ## 5. The cell function (Section 5) -/

/-- `h(A, B) = P|A - B| + μ|B + PA| - (P - μ)|B| - P(1 + μ)|A|` (Lemma 10; in Sections 9–12
`h_μ` is this function with `P = x - 1`). -/
def hcell (P μ A B : ℝ) : ℝ :=
  P * |A - B| + μ * |B + P * A| - (P - μ) * |B| - P * (1 + μ) * |A|

/-! ## 6. Equal parity: `G(Y)` and `Θ` (Section 8, eq. (G)) -/

/-- `G(Y) = ∑_{(i,j) ≠ (a,b)} |Z_{ij}| + Z_{ab}` with `Z = T_a(p) Y T_b(q)ᵀ` (the middle expression
of (G); for real `p, q` this is the definition used in Sections 8–12). -/
def Gval (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) : ℝ :=
  ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
    (if u = a ∧ v = b then triple a b p q Y u v else |triple a b p q Y u v|)

/-- `Θ = d_a(p) d_b(q) - 2 δ_a(p) δ_b(q)` (Sections 8, 10, 11). -/
def Theta (a b : ℕ) (p q : ℝ) : ℝ := dNorm a p * dNorm b q - 2 * deltaK a p * deltaK b q

/-- `Y⁻ = -s_a s_bᵀ`. -/
def Yminus (i j : ℕ) : ℝ := -(sAlt i * sAlt j)

/-- `Y⁺ = s_a s_bᵀ - 2 e_a e_bᵀ`. -/
def Yplus (a b : ℕ) (i j : ℕ) : ℝ := sAlt i * sAlt j - if i = a ∧ j = b then 2 else 0

/-- `Y = Y'` on `0..a × 0..b`. -/
def MatEq (a b : ℕ) (Y Y' : ℕ → ℕ → ℝ) : Prop := ∀ i ≤ a, ∀ j ≤ b, Y i j = Y' i j

/-- The parameter regions (eq. (regions)): `p ≥ 5, q ≥ 3` (`R₁`) or `p = 3, q ≥ 5` (`R₂`). -/
def Region1 (p q : ℝ) : Prop := 5 ≤ p ∧ 3 ≤ q

/-- Region `R₂`. -/
def Region2 (p q : ℝ) : Prop := p = 3 ∧ 5 ≤ q

/-- `(p, q)` satisfies (regions). -/
def Regions (p q : ℝ) : Prop := Region1 p q ∨ Region2 p q

/-! ## 7. Section 10: columns -/

/-- Column `j` of `Y`. -/
def col (Y : ℕ → ℕ → ℝ) (j : ℕ) : ℕ → ℝ := fun i => Y i j

/-- `Δ(c) = d_a(p) - ‖T_a(p) c‖₁`. -/
def DeltaC (a : ℕ) (p : ℝ) (c : ℕ → ℝ) : ℝ := dNorm a p - l1 a (tMulVec a p c)

/-- `ω_i`: the sum of the absolute values of the entries of row `i` of `T_a(p)`. -/
def rowAbsSum (a : ℕ) (p : ℝ) (i : ℕ) : ℝ := ∑ k ∈ range (a + 1), |tEntry a p i k|

/-- `ψ_μ(c, ζ) = P(1 + μ) Δ(c) - ∑_{i=0}^{a} h_μ((Mc)_i, (Mζ)_i)`, `M = T_a(p)`, `P = q - 1`. -/
def psi (a : ℕ) (p q μ : ℝ) (c ζ : ℕ → ℝ) : ℝ :=
  (q - 1) * (1 + μ) * DeltaC a p c -
    ∑ i ∈ range (a + 1), hcell (q - 1) μ (tMulVec a p c i) (tMulVec a p ζ i)

/-- The column path `ζ_j` (`-1 ≤ j ≤ b - 1`): `ζ_{b-1} = c_b`, `ζ_{j-1} = (ζ_j + P c_j)/x`, i.e.
row by row the path of Section 3 with `x = q`, `k = b`. -/
def zetaPath (b : ℕ) (q : ℝ) (Y : ℕ → ℕ → ℝ) (j : ℤ) : ℕ → ℝ := fun i => z q b (fun l => Y i l) j

/-- `ψ_j = ψ_{μ_{j-1}}(c_j, ζ_j)` (`μ` is the potential for `x = q`). -/
def psiCol (a b : ℕ) (p q : ℝ) (Y : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  psi a p q (mu q ((j : ℤ) - 1)) (col Y j) (zetaPath b q Y j)

/-- `g₊ = (-1)^a s_a - 2 e_a`. -/
def gPlus (a : ℕ) (i : ℕ) : ℝ := (-1) ^ a * sAlt i - if i = a then 2 else 0

/-- `t⁻ = max(-t, 0)`. -/
def negPt (t : ℝ) : ℝ := max (-t) 0

/-! ## 8. Section 12: the reduction (Proposition 31) -/

/-- `μ_∞ = P / (x + 1)` for `x = q`, `P = q - 1`. -/
def muInf (q : ℝ) : ℝ := (q - 1) / (q + 1)

/-- `η_0(y) = y`, `η_{n+1}(y) = (P - η_n(y)) / x`. -/
def etaMap (q : ℝ) : ℕ → ℝ → ℝ
  | 0, y => y
  | n + 1, y => (q - 1 - etaMap q n y) / q

/-- The set `𝓕_a` of triples `(μ, m, r)` (Section 12), for `x = q`. -/
def FamF (a : ℕ) (q : ℝ) (t : ℝ × ℝ × ℝ) : Prop :=
  let μ0 := mu q 0; let μ1 := mu q 1; let L := muInf q; let P := q - 1
  if Even a then
    (t.1 = 1 ∧ μ0 ≤ t.2.1 ∧ t.2.1 ≤ L ∧ t.2.2 = (P - t.2.1) / q) ∨
    (t.2.1 = 1 ∧ μ0 ≤ t.1 ∧ t.1 ≤ L ∧ t.2.2 = (P - t.1) / q) ∨
    (L ≤ t.1 ∧ t.1 ≤ μ1 ∧ μ0 ≤ t.2.1 ∧ t.2.1 ≤ L ∧ t.2.2 = t.1) ∨
    (μ0 ≤ t.1 ∧ t.1 ≤ L ∧ L ≤ t.2.1 ∧ t.2.1 ≤ μ1 ∧ t.2.2 = t.2.1)
  else
    (t.1 = 1 ∧ t.2.1 = 1 ∧ t.2.2 = μ0) ∨
    (t.1 = 1 ∧ L ≤ t.2.1 ∧ t.2.1 ≤ μ1 ∧ t.2.2 = (P - t.2.1) / q) ∨
    (t.2.1 = 1 ∧ L ≤ t.1 ∧ t.1 ≤ μ1 ∧ t.2.2 = (P - t.1) / q) ∨
    (((μ0 ≤ t.1 ∧ t.1 ≤ L ∧ μ0 ≤ t.2.1 ∧ t.2.1 ≤ L) ∨
      (L ≤ t.1 ∧ t.1 ≤ μ1 ∧ L ≤ t.2.1 ∧ t.2.1 ≤ μ1)) ∧ t.2.2 = L)

/-- Condition (S_a) at `(p, q)` with `P_min = Pm`. -/
def CondS (a : ℕ) (p Pm : ℝ) : Prop :=
  ∀ c : ℕ → ℝ, IsSignVec a c → ¬ IsPmAlt a c →
    Pm * DeltaC a p c >
      ∑ i ∈ range (a + 1), max 0 (rowAbsSum a p i - Pm * |tMulVec a p c i|)

/-- Condition (F_a) at `(p, q)`. -/
def CondF (a : ℕ) (p q : ℝ) : Prop :=
  ∀ c : ℕ → ℝ, IsSignVec a c → ¬ (∀ i ≤ a, c i = -sAlt i) →
    ∀ t : ℝ × ℝ × ℝ, FamF a q t →
      psi a p q t.1 c (fun i => t.2.1 * sAlt i) > 2 * q * deltaK a p * t.2.2

/-- The interval `I_k` of (C1): `[μ_0, μ_∞]` if `k ≡ a (mod 2)`, else `[μ_∞, μ_1] ∪ {1}`. -/
def Ik (a k : ℕ) (q y : ℝ) : Prop :=
  if k % 2 = a % 2 then mu q 0 ≤ y ∧ y ≤ muInf q
  else (muInf q ≤ y ∧ y ≤ mu q 1) ∨ y = 1

/-- `D̂_1 = d_1(x)/x = (3x - 4)/x`. -/
def Dhat1 (q : ℝ) : ℝ := (3 * q - 4) / q

/-- `D̂_2 = d_2(x)/x² = (5x² - 8x + 4)/x²`. -/
def Dhat2 (q : ℝ) : ℝ := (5 * q ^ 2 - 8 * q + 4) / q ^ 2

/-- Condition (C_a) at `(p, q)`. -/
def CondC (a : ℕ) (p q : ℝ) : Prop :=
  ∀ g : ℕ → ℝ, IsSignVec a g → g a = -1 →
    ¬ (∀ i ≤ a, g i = -((-1) ^ a * sAlt i)) → ¬ (∀ i ≤ a, g i = gPlus a i) →
    DeltaC a p g > 2 * deltaK a p ∨
    (let γ := 2 * deltaK a p - DeltaC a p g
     let P := q - 1
     -- (C1)
     (∀ k ≤ 4, ∀ y : ℝ, Ik a k q y → ∀ c : ℕ → ℝ, IsSignVec a c →
        ¬ (∀ i ≤ a, c i = (-1) ^ (k + 1) * g i) →
        ∑ n ∈ Finset.Icc 1 k, P * (1 + etaMap q n y) * DeltaC a p g +
            psi a p q y c (fun i => (-1) ^ k * mu q ((k : ℤ) - 1) * g i) >
          q * etaMap q (k + 1) y * γ) ∧
     -- (C2)
     (∀ y : ℝ, (if Even a then mu q 0 ≤ y ∧ y ≤ muInf q else muInf q ≤ y ∧ y ≤ mu q 1) →
        ∑ n ∈ range 5, P * (1 + etaMap q n y) * DeltaC a p g > q * etaMap q 5 y * γ) ∧
     -- (C3)
     (if Even a then DeltaC a p g * (Dhat1 q / mu q 1 + 2) > 2 * deltaK a p
      else DeltaC a p g * Dhat1 q / mu q 0 > 2 * deltaK a p ∧
        DeltaC a p g * (Dhat2 q / muInf q + 2) > 2 * deltaK a p))

/-- The three conditions of Proposition 31 at `(p, q)` with `P_min = Pm`. -/
def CondAll (a : ℕ) (p q Pm : ℝ) : Prop := CondS a p Pm ∧ CondF a p q ∧ CondC a p q

/-- Conclusion of Proposition 31 (and of Theorem 25 for `a = 2`) at `(p, q)`. -/
def SignConclusion (a : ℕ) (p q : ℝ) : Prop :=
  ∀ b : ℕ, 1 ≤ b → b % 2 = a % 2 → ∀ Y : ℕ → ℕ → ℝ, IsSignMat a b Y → Y a b = -1 →
    Gval a b p q Y ≤ Theta a b p q ∧
      (Gval a b p q Y = Theta a b p q ↔ MatEq a b Y Yminus ∨ MatEq a b Y (Yplus a b))

/-! ## 9. Statements: Section 1 -/

/-- **Theorem 1** (Jiang–Yang, Theorem A; reproved in the paper via Remark 13). -/
def Theorem1 : Prop :=
  ∀ p q r s : ℕ, DistinctOddPrimes p q → 5 ≤ q → 1 ≤ r →
    MaxEnergy (p ^ (2 * r) * q ^ (2 * s + 1))
      ((((p ^ (2 * r) * q ^ (2 * s + 1) : ℕ) : ℝ) +
          dClosed (2 * r) p * dClosed (2 * s + 1) q) / 2)
      {evenSet p q (2 * r) (2 * s + 1)}

/-- **Theorem 2** (main theorem, `q = 3`). -/
def Theorem2 : Prop :=
  ∀ p r s : ℕ, p.Prime → 5 ≤ p → 1 ≤ r →
    MaxEnergy (p ^ (2 * r) * 3 ^ (2 * s + 1))
      ((((p ^ (2 * r) * 3 ^ (2 * s + 1) : ℕ) : ℝ) +
          dClosed (2 * r) p * dClosed (2 * s + 1) 3) / 2)
      {evenSet p 3 (2 * r) (2 * s + 1)}

/-- **Theorem 3** (`n = p q^m` and `n = p^m q`, `m` odd). -/
def Theorem3 : Prop :=
  ∀ p q m : ℕ, DistinctOddPrimes p q → 1 ≤ m → Odd m →
    MaxEnergy (p * q ^ m)
      ((((p * q ^ m : ℕ) : ℝ) + (3 * (p : ℝ) - 4) * dClosed m q) / 2 - ((p : ℝ) - 2) * deltaK m q)
      {oddSet p q 1 m, (evenSet p q 1 m).erase (p * q ^ m)} ∧
    MaxEnergy (p ^ m * q)
      ((((p ^ m * q : ℕ) : ℝ) + (3 * (q : ℝ) - 4) * dClosed m p) / 2 - ((q : ℝ) - 2) * deltaK m p)
      {oddSet p q m 1, (evenSet p q m 1).erase (p ^ m * q)}

/-- **Theorem 4** (`n = p² q^b` and `n = p^b q²`, `b ≥ 2` even). -/
def Theorem4 : Prop :=
  ∀ p q b : ℕ, DistinctOddPrimes p q → 2 ≤ b → Even b →
    MaxEnergy (p ^ 2 * q ^ b)
      ((((p ^ 2 * q ^ b : ℕ) : ℝ) + (5 * (p : ℝ) ^ 2 - 8 * p + 4) * dClosed b q) / 2 -
        ((p : ℝ) ^ 2 - 2 * p + 2) * deltaK b q)
      {oddSet p q 2 b, (evenSet p q 2 b).erase (p ^ 2 * q ^ b)} ∧
    MaxEnergy (p ^ b * q ^ 2)
      ((((p ^ b * q ^ 2 : ℕ) : ℝ) + (5 * (q : ℝ) ^ 2 - 8 * q + 4) * dClosed b p) / 2 -
        ((q : ℝ) ^ 2 - 2 * q + 2) * deltaK b p)
      {oddSet p q b 2, (evenSet p q b 2).erase (p ^ b * q ^ 2)}

/-- **Summary claim of the abstract and Section 1** ("this settles the maximal-energy problem for
opposite-parity exponents for all pairs of distinct odd primes"): for distinct odd primes `p, q`
and `a, b ≥ 1` with `a + b` odd, the maximal energy for `n = p^a q^b` is `½[n + d_a(p) d_b(q)]`,
uniquely attained by `{p^i q^j : i + j even}`. (A consequence of Theorems 1 and 2, with the names
of the primes exchanged when the even exponent belongs to `q`.) -/
def SummaryOppositeParity : Prop :=
  ∀ p q a b : ℕ, DistinctOddPrimes p q → 1 ≤ a → 1 ≤ b → Odd (a + b) →
    MaxEnergy (p ^ a * q ^ b)
      ((((p ^ a * q ^ b : ℕ) : ℝ) + dClosed a p * dClosed b q) / 2)
      {evenSet p q a b}

/-- The claim of Conjecture 14 for one exponent pair `(a, b)`: for all distinct odd primes. -/
def EqualParityClaim (a b : ℕ) : Prop :=
  ∀ p q : ℕ, DistinctOddPrimes p q →
    MaxEnergy (p ^ a * q ^ b)
      ((((p ^ a * q ^ b : ℕ) : ℝ) + dClosed a p * dClosed b q) / 2 - deltaK a p * deltaK b q)
      {oddSet p q a b, (evenSet p q a b).erase (p ^ a * q ^ b)}

/-- **Theorem 5, narrow revision**: same parity, min(a,b) ≤ 2; the other exponent is unbounded. -/
def Theorem5MinTwo : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → Even (a + b) → min a b ≤ 2 → EqualParityClaim a b

/-! ## 10. Statements: Sections 2–6 -/

/-- **Proposition 6** (Jiang–Yang, Proposition 2.2): `E(ICG_n(D)) = ‖T_a(p) X T_b(q)ᵀ‖₁`.
Stated for every set `D` of proper divisors (the paper's `D` is also nonempty). -/
def Proposition6 : Prop :=
  ∀ p q a b : ℕ, p.Prime → q.Prime → p ≠ q → 1 ≤ a → 1 ≤ b →
    ∀ D : Finset ℕ, D ⊆ (p ^ a * q ^ b).properDivisors →
      energy (p ^ a * q ^ b) D = l1Mat a b (triple a b p q (divMat p q D))

/-- **Lemma 7** (path identity). Standing assumptions of Section 2: real `x > 1`, `k ≥ 1`. -/
def Lemma7 : Prop :=
  ∀ (x : ℝ), 1 < x → ∀ k : ℕ, 1 ≤ k → ∀ w : ℕ → ℝ,
    l1 k (tMulVec k x w) =
      x ^ k * (|z x k w (-1)| + ∑ j ∈ range k, |z x k w ((j : ℤ) - 1) - z x k w j|)

/-- **Lemma 8** (one-dimensional potential). -/
def Lemma8 : Prop :=
  ∀ (x : ℝ), 2 < x → ∀ k : ℕ, 1 ≤ k → ∀ y : ℕ → ℝ, IsSignVec k y →
    -- `sgn z_j = y_{j+1}` and `(x-2)/x ≤ |z_j| ≤ 1` for `-1 ≤ j ≤ k - 1` (here `j + 1 = i`)
    (∀ i ≤ k, 0 < y i * z x k y ((i : ℤ) - 1) ∧
        (x - 2) / x ≤ |z x k y ((i : ℤ) - 1)| ∧ |z x k y ((i : ℤ) - 1)| ≤ 1) ∧
    -- the identity
    l1 k (tMulVec k x y) / x ^ k =
      ∑ j ∈ range k, cc x j + mu x ((k : ℤ) - 1) -
        ∑ j ∈ NA k y, 2 * mu x j * |z x k y j| ∧
    -- consequences
    l1 k (tMulVec k x y) ≤ dNorm k x ∧
    (l1 k (tMulVec k x y) = dNorm k x ↔ IsPmAlt k y) ∧
    dNorm k x = x ^ k * (∑ j ∈ range k, cc x j + mu x ((k : ℤ) - 1)) ∧
    0 < tMulVec k x sAlt k

/-- **Remark 9** (closed forms), for all real `x > 2` and all `k ≥ 0`:
`x^k μ_{k-1} = δ_k(x)`; `(T_k(x) s_k)_k = δ_k(x)`; `d_{k+1} = x d_k + 2 δ_{k+1}`;
`‖T_k(x) s_k‖₁` equals the closed form of Theorem 1; and
`δ_k(x) = x^k + 2 ∑_{i<k} (-1)^{k-i} x^i` (the form used in the proof of Proposition 15). -/
def Remark9 : Prop :=
  ∀ (x : ℝ), 2 < x → ∀ k : ℕ,
    x ^ k * mu x ((k : ℤ) - 1) = deltaK k x ∧
    tMulVec k x sAlt k = deltaK k x ∧
    dNorm (k + 1) x = x * dNorm k x + 2 * deltaK (k + 1) x ∧
    dNorm k x = dClosed k x ∧
    deltaK k x = x ^ k + 2 * ∑ i ∈ range k, (-1) ^ (k - i) * x ^ i

/-- **Lemma 10** (a two-variable inequality). -/
def Lemma10 : Prop :=
  ∀ P μ : ℝ, μ ≤ P → 0 ≤ μ → μ ≤ 1 → ∀ A B : ℝ,
    hcell P μ A B ≤ 2 * μ * max 0 (|B| - P * |A|)

/-- **Lemma 11** (local inequality). `F(w) = ‖T_b(q) w‖₁`, `D = d_b(q)`. -/
def Lemma11 : Prop :=
  ∀ q : ℝ, 3 ≤ q → ∀ b : ℕ, 1 ≤ b → ∀ P μ : ℝ, 4 ≤ P → 3 / 5 ≤ μ → μ ≤ 1 →
    ∀ y ζ : ℕ → ℝ, IsSignVec b y → (∀ i ≤ b, |ζ i| ≤ 1) →
      let F : (ℕ → ℝ) → ℝ := fun w => l1 b (tMulVec b q w)
      let Λ := P * F (fun i => y i - ζ i) + μ * F (fun i => ζ i + P * y i) - (P - μ) * F ζ
      Λ ≤ P * (1 + μ) * dNorm b q ∧ (¬ IsPmAlt b y → Λ < P * (1 + μ) * dNorm b q)

/-- **Theorem 12** (sign-matrix inequality). -/
def Theorem12 : Prop :=
  ∀ p q : ℝ, 5 ≤ p → 3 ≤ q → ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ∀ Y : ℕ → ℕ → ℝ, IsSignMat a b Y →
    l1Mat a b (triple a b p q Y) ≤ dNorm a p * dNorm b q ∧
      (l1Mat a b (triple a b p q Y) = dNorm a p * dNorm b q ↔ IsPmCheckerboard a b Y)

/-- **Remark 13** (exchanged form of Theorem 12): it holds whenever `min(p, q) ≥ 3` and
`max(p, q) ≥ 5`. (That the deduction of Section 7 then proves Theorem 1 is `Theorem1`.) -/
def Remark13 : Prop :=
  ∀ p q : ℝ, 3 ≤ min p q → 5 ≤ max p q → ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ∀ Y : ℕ → ℕ → ℝ, IsSignMat a b Y →
      l1Mat a b (triple a b p q Y) ≤ dNorm a p * dNorm b q ∧
        (l1Mat a b (triple a b p q Y) = dNorm a p * dNorm b q ↔ IsPmCheckerboard a b Y)

/-! ## 11. Statements: Section 8 -/

/-- **Section 8** (unnumbered claim): for every equal-parity shape, `{p^i q^j : i + j odd}` is
admissible and has energy `½[n + d_a(p) d_b(q)] - δ_a(p) δ_b(q)`, and no admissible set reaches
`½[n + d_a(p) d_b(q)]` ("the energy bound … is not attained"; "the first of the two sets always
attains the conjectured value"). Holds for all `a, b ≥ 1` with `a + b` even. -/
def Section8OddSet : Prop :=
  ∀ p q a b : ℕ, DistinctOddPrimes p q → 1 ≤ a → 1 ≤ b → Even (a + b) →
    IsConnSet (p ^ a * q ^ b) (oddSet p q a b) ∧
    energy (p ^ a * q ^ b) (oddSet p q a b) =
      (((p ^ a * q ^ b : ℕ) : ℝ) + dClosed a p * dClosed b q) / 2 - deltaK a p * deltaK b q ∧
    ∀ D : Finset ℕ, IsConnSet (p ^ a * q ^ b) D →
      energy (p ^ a * q ^ b) D < (((p ^ a * q ^ b : ℕ) : ℝ) + dClosed a p * dClosed b q) / 2

/-- **Conjecture 14** — NOT claimed by the paper; stated for reference only. -/
def Conjecture14 : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → Even (a + b) → EqualParityClaim a b

/-- Le–Sander's multiplicative divisor sets of `n = p^a q^b` ([LS], cited in Remark 16):
`D = {p^i q^j : i ∈ A, j ∈ B}` for some `A ⊆ {0, …, a}` and `B ⊆ {0, …, b}`, i.e. `D = D₁ D₂` with
`D₁` a set of divisors of `p^a` and `D₂` a set of divisors of `q^b`. (Historical note: the first draft
used a reviewer formulation before [LS] was accessible. The later independent freeze-review.md
§3.2 records checking [LS] pp.1409–1411; legal-domain equivalence is a separate supplement.) -/
def IsMultSet (p q a b : ℕ) (D : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ, A ⊆ range (a + 1) ∧ B ⊆ range (b + 1) ∧
    D = (A ×ˢ B).image (fun ij => p ^ ij.1 * q ^ ij.2)

/-- `Ẽ_max(p^a q^b) = V`: `V` is the largest energy of `ICG_n(D)` over the nonempty multiplicative
sets `D` of proper divisors of `n = p^a q^b`. -/
def MultMaxEnergy (p q a b : ℕ) (V : ℝ) : Prop :=
  (∃ D : Finset ℕ, IsConnSet (p ^ a * q ^ b) D ∧ IsMultSet p q a b D ∧
      energy (p ^ a * q ^ b) D = V) ∧
    ∀ D : Finset ℕ, IsConnSet (p ^ a * q ^ b) D → IsMultSet p q a b D →
      energy (p ^ a * q ^ b) D ≤ V

/-- **Remark 16** (the case `n = pq` and two orders `pq³`):
(i) the maximal energy for `n = pq` is `4(p-1)(q-1)`, attained exactly by `{p, q}` and `{1}`;
(ii) `E(ICG_pq({1})) = E(ICG_pq({p,q})) = 4φ(pq)`, `E(ICG_pq({p})) = E(ICG_pq({1,p})) = 2p(q-1)`
(and symmetrically for `{q}`, `{1,q}`), `E(ICG_pq({1,p,q})) = 2(pq - 1)`;
(iii) `E_max(5·3³) = 584` and `E_max(3·5³) = 1632`, attained exactly by the two sets of Theorem 3;
(iv) for `n = pq` the maximum over multiplicative divisor sets (Le–Sander's `Ẽ_max`) is also
`4(p-1)(q-1)`, so `E_max(pq) = Ẽ_max(pq)`;
(v) `Ẽ_max(5·3³) = 512` and `Ẽ_max(3·5³) = 1472` (so `E_max > Ẽ_max` there);
(vi) the maximisers in (iii) are not multiplicative.
Le–Sander's general results (their closed formula for `Ẽ_max`, `E_max ≥ Ẽ_max`) are cited, not
claimed. -/
def Remark16 : Prop :=
  (∀ p q : ℕ, DistinctOddPrimes p q →
    MaxEnergy (p * q) (4 * ((p : ℝ) - 1) * ((q : ℝ) - 1)) {{p, q}, {1}} ∧
    MultMaxEnergy p q 1 1 (4 * ((p : ℝ) - 1) * ((q : ℝ) - 1)) ∧
    energy (p * q) {1} = 4 * (Nat.totient (p * q) : ℝ) ∧
    energy (p * q) {p, q} = 4 * (Nat.totient (p * q) : ℝ) ∧
    energy (p * q) {p} = 2 * p * ((q : ℝ) - 1) ∧
    energy (p * q) {1, p} = 2 * p * ((q : ℝ) - 1) ∧
    energy (p * q) {q} = 2 * q * ((p : ℝ) - 1) ∧
    energy (p * q) {1, q} = 2 * q * ((p : ℝ) - 1) ∧
    energy (p * q) {1, p, q} = 2 * ((p * q : ℕ) - 1 : ℝ)) ∧
  MaxEnergy (5 * 3 ^ 3) 584 {oddSet 5 3 1 3, (evenSet 5 3 1 3).erase (5 * 3 ^ 3)} ∧
  MaxEnergy (3 * 5 ^ 3) 1632 {oddSet 3 5 1 3, (evenSet 3 5 1 3).erase (3 * 5 ^ 3)} ∧
  MultMaxEnergy 5 3 1 3 512 ∧ MultMaxEnergy 3 5 1 3 1472 ∧
  ¬ IsMultSet 5 3 1 3 (oddSet 5 3 1 3) ∧
  ¬ IsMultSet 5 3 1 3 ((evenSet 5 3 1 3).erase (5 * 3 ^ 3)) ∧
  ¬ IsMultSet 3 5 1 3 (oddSet 3 5 1 3) ∧
  ¬ IsMultSet 3 5 1 3 ((evenSet 3 5 1 3).erase (3 * 5 ^ 3))

/-- **Remark 17** (a near-maximal set): for every prime `p ≥ 5`, `q = 3`,
`D = {1, 3, p², 3p², 9p}` has energy `62p² - 90p + 40 - 2(p - 3)`, and the maximal energy for
`n = 9p²` is `62p² - 90p + 40`. -/
def Remark17 : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    energy (p ^ 2 * 3 ^ 2) {1, 3, p ^ 2, 3 * p ^ 2, 9 * p} =
        62 * (p : ℝ) ^ 2 - 90 * p + 40 - 2 * ((p : ℝ) - 3) ∧
    MaxEnergy (p ^ 2 * 3 ^ 2) (62 * (p : ℝ) ^ 2 - 90 * p + 40)
      {oddSet p 3 2 2, (evenSet p 3 2 2).erase (p ^ 2 * 3 ^ 2)}

/-! ## 12. Statements: Section 9 (proof of Theorem 3) -/

/-- The parameter range of Section 9: `x ≥ 5, R ≥ 2` or `x = 3, R ≥ 4`. -/
def ParamXR (x R : ℝ) : Prop := (5 ≤ x ∧ 2 ≤ R) ∨ (x = 3 ∧ 4 ≤ R)

/-- **Lemma 18**: `ν(w) = ∑_{j=0}^{m} ĉ_j |w_j| + (1/x) ∑_{j<m} h_{μ_{j-1}}(w_j, z_j(w))`, with
`ν(w) = ‖T_m(x) w‖₁ / x^m`, `ĉ_j = c_j` (`j < m`), `ĉ_m = ρ = μ_{m-1}`, `h_μ = hcell (x-1) μ`.
Stated for all real `x > 1` and all `m ≥ 1` (the paper uses `x = q ≥ 3`; Section 10 says the proof
does not use that `m` is odd). -/
def Lemma18 : Prop :=
  ∀ (x : ℝ), 1 < x → ∀ m : ℕ, 1 ≤ m → ∀ w : ℕ → ℝ,
    l1 m (tMulVec m x w) / x ^ m =
      ∑ j ∈ range m, cc x j * |w j| + mu x ((m : ℤ) - 1) * |w m| +
        (1 / x) * ∑ j ∈ range m, hcell (x - 1) (mu x ((j : ℤ) - 1)) (w j) (z x m w j)

/-- **Lemma 19**: `ν(y) - |z_{-1}(y)| ≤ D̂ - ρ`, with equality exactly for `y = ±s_m`.
(`D̂ = d_m(x)/x^m`, `ρ = μ_{m-1}`.) Stated for real `x > 2` and all `m ≥ 1`. -/
def Lemma19 : Prop :=
  ∀ (x : ℝ), 2 < x → ∀ m : ℕ, 1 ≤ m → ∀ y : ℕ → ℝ, IsSignVec m y →
    let lhs := l1 m (tMulVec m x y) / x ^ m - |z x m y (-1)|
    let rhs := dNorm m x / x ^ m - mu x ((m : ℤ) - 1)
    lhs ≤ rhs ∧ (lhs = rhs ↔ IsPmAlt m y)

/-- **Lemma 20** (parity defect): `(3R - 1) σ(y) > (R - 1) ρ` for sign vectors with `y_0 = y_m`,
`m` odd, where `σ(y) = ∑_{j ∈ NA(y)} μ_j |z_j(y)|`. -/
def Lemma20 : Prop :=
  ∀ x R : ℝ, ParamXR x R → ∀ m : ℕ, 1 ≤ m → Odd m → ∀ y : ℕ → ℝ, IsSignVec m y → y 0 = y m →
    (3 * R - 1) * (∑ j ∈ NA m y, mu x j * |z x m y j|) > (R - 1) * mu x ((m : ℤ) - 1)

/-! ## 13. Statements: Section 10 (standing assumptions: `a ≥ 2`, `b ≥ 1`, `a + b` even,
`(p, q)` satisfies (regions)) -/

/-- **Lemma 21** (column identity):
`x^{1-b}(Θ - G(Y)) = ∑_{j<b} ψ_j + xρ(Δ(c_b) - 2δ_a(p)) + 2x((Mζ_{-1})_a)⁻`. -/
def Lemma21 : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 1 ≤ b → Even (a + b) → ∀ p q : ℝ, Regions p q →
    ∀ Y : ℕ → ℕ → ℝ, IsSignMat a b Y →
      q ^ (1 - (b : ℤ)) * (Theta a b p q - Gval a b p q Y) =
        ∑ j ∈ range b, psiCol a b p q Y j +
          q * mu q ((b : ℤ) - 1) * (DeltaC a p (col Y b) - 2 * deltaK a p) +
          2 * q * negPt (tMulVec a p (zetaPath b q Y (-1)) a)

/-- **Lemma 22** (one column). -/
def Lemma22 : Prop :=
  ∀ a : ℕ, 2 ≤ a → ∀ p q : ℝ, Regions p q → ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 →
    ∀ c ζ : ℕ → ℝ, IsSignVec a c → (∀ i ≤ a, |ζ i| ≤ 1) →
      psi a p q μ c ζ ≥ (q - 1) * (1 + μ) * DeltaC a p c -
          2 * μ * ∑ i ∈ range (a + 1), max 0 (|tMulVec a p ζ i| - (q - 1) * |tMulVec a p c i|) ∧
      (IsPmAlt a c →
        (∀ i ≤ a, hcell (q - 1) μ (tMulVec a p c i) (tMulVec a p ζ i) ≤ 0) ∧
        psi a p q μ c ζ ≥ 0 ∧
        (psi a p q μ c ζ = 0 ↔
          ∀ i ≤ a, hcell (q - 1) μ (tMulVec a p c i) (tMulVec a p ζ i) = 0))

/-- **Lemma 23** (chains). -/
def Lemma23 : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 1 ≤ b → Even (a + b) → ∀ p q : ℝ, Regions p q →
    ∀ Y : ℕ → ℕ → ℝ, IsSignMat a b Y →
      (∀ g : ℕ → ℝ, IsSignVec a g → ∀ k ≤ b,
        (∀ i ≤ a, Y i b = g i) → (∀ l, 1 ≤ l → l ≤ k → ∀ i ≤ a, Y i (b - l) = (-1) ^ l * g i) →
        (∀ l ≤ k, ∀ i ≤ a,
          zetaPath b q Y ((b : ℤ) - 1 - l) i = (-1) ^ l * mu q ((l : ℤ) - 1) * g i) ∧
        (∀ l, 1 ≤ l → l ≤ k →
          psiCol a b p q Y (b - l) = (q - 1) * (1 + mu q ((b : ℤ) - l - 1)) * DeltaC a p g)) ∧
      (∀ J : ℕ, J < b → (∀ l, J < l → l ≤ b → ∀ i ≤ a, Y i l = (-1) ^ (l + 1) * sAlt i) →
        ∀ i ≤ a, zetaPath b q Y J i = (-1) ^ J * mu q ((b : ℤ) - 2 - J) * sAlt i)

/-- **Lemma 24** (the second extremal matrix). -/
def Lemma24 : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 1 ≤ b → Even (a + b) → ∀ p q : ℝ, Regions p q →
    DeltaC a p (gPlus a) = 2 * deltaK a p ∧
    (∀ j < b, psiCol a b p q (Yplus a b) j = 0) ∧
    0 < tMulVec a p (zetaPath b q (Yplus a b) (-1)) a ∧
    Gval a b p q (Yplus a b) = Theta a b p q ∧
    (∀ Y : ℕ → ℕ → ℝ, IsSignMat a b Y → (∀ i ≤ a, Y i b = gPlus a i) →
      (∀ j < b, IsPmAlt a (col Y j) ∧ psiCol a b p q Y j = 0) → MatEq a b Y (Yplus a b))

/-! ## 14. Statements: Section 11 (`a = 2`) -/

/-- **Theorem 25** (sign-matrix inequality for the exponent 2). -/
def Theorem25 : Prop :=
  ∀ b : ℕ, 2 ≤ b → Even b → ∀ p q : ℝ, Regions p q →
    ∀ Y : ℕ → ℕ → ℝ, IsSignMat 2 b Y → Y 2 b = -1 →
      Gval 2 b p q Y ≤ Theta 2 b p q ∧
        (Gval 2 b p q Y = Theta 2 b p q ↔ MatEq 2 b Y Yminus ∨ MatEq 2 b Y (Yplus 2 b))

/-- `g₃ = (1, -1, -1)` and `g₄ = (1, 1, 1)` (Section 11). -/
def g3 (i : ℕ) : ℝ := if i = 0 then 1 else -1

/-- `g₄ = (1, 1, 1)`. -/
def g4 (_i : ℕ) : ℝ := 1

/-- `g₂ = (1, 1, -1)`. -/
def g2 (i : ℕ) : ℝ := if i = 2 then -1 else 1

/-- `c = ±g` on `0..2`. -/
def IsPm3 (c g : ℕ → ℝ) : Prop := (∀ i ≤ 2, c i = g i) ∨ (∀ i ≤ 2, c i = -g i)

/-- **Lemma 26** (columns for `a = 2`); `R = p - 1`, `P = q - 1`, `B = Mζ`. -/
def Lemma26 : Prop :=
  ∀ p q : ℝ, Regions p q → ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → ∀ ζ : ℕ → ℝ, (∀ i ≤ 2, |ζ i| ≤ 1) →
    (∀ c : ℕ → ℝ, IsSignVec 2 c → ¬ IsPmAlt 2 c → psi 2 p q μ c ζ > 0) ∧
    (∀ c : ℕ → ℝ, IsPm3 c g3 →
      psi 2 p q μ c ζ ≥ 2 * (q - 1) * (1 + μ) * ((p - 1) ^ 2 + 1) - 2 * μ * |tMulVec 2 p ζ 0|) ∧
    (∀ c : ℕ → ℝ, IsPm3 c g4 →
      psi 2 p q μ c ζ ≥ 4 * (q - 1) * (p - 1) ^ 2 * (1 + μ) -
        2 * μ * (|tMulVec 2 p ζ 0| + |tMulVec 2 p ζ 1|))

/-- **Lemma 27** (eight polynomial inequalities); `T = (R² + 1)(P² + 1)`. -/
def Lemma27 : Prop :=
  ∀ R P : ℝ, ((4 ≤ R ∧ 2 ≤ P) ∨ (R = 2 ∧ 4 ≤ P)) →
    let T := (R ^ 2 + 1) * (P ^ 2 + 1)
    (P - 1) ^ 2 * (5 * R ^ 2 + 2 * R + 1) > T ∧
    P * (P + 1) * (R - 1) ^ 2 + (P - 1) ^ 2 * (3 * R ^ 2 + 1) > T ∧
    (R ^ 2 + 1) * (P - 1) + (P + 1) * (2 * P * (R ^ 2 - R + 1) - 3 * R ^ 2 - 1) > 0 ∧
    P * (P + 1) * (R - 1) ^ 2 + 2 * (P - 1) ^ 2 * R * (R + 1) > T ∧
    (P + 1) * (P * (R - 1) ^ 2 + 2 * P ^ 2 * (R + 1)) > T ∧
    (4 ≤ R → (P + 1) * (2 * P * R * (R - 3) + 2 * P ^ 2 * (R + 1)) > T) ∧
    P * (P + 1) ^ 2 * (R ^ 2 + 1) > 2 * R * (R + 1) * (P ^ 2 + 1) ∧
    2 * R * (P * R - 1) * (P + 1) > T

/-- **Lemma 28**: `b` even, `0 ≤ J < b`, `μ = μ_{J-1}`, `m = μ_{b-2-J}`: for every column
`c ≠ -s_2`, `ψ_μ(c, m s_2) > 2x δ_2(p) ρ` (`x = q`, `ρ = μ_{b-1}`). -/
def Lemma28 : Prop :=
  ∀ b : ℕ, 2 ≤ b → Even b → ∀ p q : ℝ, Regions p q → ∀ J : ℕ, J < b →
    ∀ c : ℕ → ℝ, IsSignVec 2 c → ¬ (∀ i ≤ 2, c i = -sAlt i) →
      psi 2 p q (mu q ((J : ℤ) - 1)) c (fun i => mu q ((b : ℤ) - 2 - J) * sAlt i) >
        2 * q * deltaK 2 p * mu q ((b : ℤ) - 1)

/-- **Lemma 29**: `b` even; if `c_b = g₂` then `∑_{j<b} ψ_j > 4R x ρ`. -/
def Lemma29 : Prop :=
  ∀ b : ℕ, 2 ≤ b → Even b → ∀ p q : ℝ, Regions p q → ∀ Y : ℕ → ℕ → ℝ, IsSignMat 2 b Y →
    (∀ i ≤ 2, Y i b = g2 i) →
      ∑ j ∈ range b, psiCol 2 b p q Y j > 4 * (p - 1) * q * mu q ((b : ℤ) - 1)

/-- **Remark 30** (two tight families): (i) `b = 2`, `q = 3`, `Y = s_2 (1,1,-1)ᵀ`:
`Θ - G(Y) = 4(p - 3)` for real `p ≥ 5`; (ii) `p = 3`, `Y = (1,1,-1)ᵀ s_bᵀ` (`b ≥ 2` even, real
`q ≥ 5`): `Θ - G(Y) = 2(d_b(q) - 5 δ_b(q))`, which is `4(q - 3)` for `b = 2`. -/
def Remark30 : Prop :=
  (∀ p : ℝ, 5 ≤ p →
    Theta 2 2 p 3 - Gval 2 2 p 3 (fun i j => sAlt i * g2 j) = 4 * (p - 3)) ∧
  (∀ q : ℝ, 5 ≤ q → ∀ b : ℕ, 2 ≤ b → Even b →
    Theta 2 b 3 q - Gval 2 b 3 q (fun i j => g2 i * sAlt j) =
      2 * (dNorm b q - 5 * deltaK b q)) ∧
  (∀ q : ℝ, 5 ≤ q → 2 * (dNorm 2 q - 5 * deltaK 2 q) = 4 * (q - 3))

/-! ## 15. Statements: Section 12 -/

/-- **Proposition 31** (reduction to finitely many inequalities), for `R₁` (`P_min = 2`) and
`R₂` (`P_min = 4`). -/
def Proposition31 : Prop :=
  ∀ a : ℕ, 2 ≤ a →
    ((∀ p q : ℝ, Region1 p q → CondAll a p q 2) → ∀ p q : ℝ, Region1 p q → SignConclusion a p q) ∧
    ((∀ p q : ℝ, Region2 p q → CondAll a p q 4) → ∀ p q : ℝ, Region2 p q → SignConclusion a p q)

end BackfillPaper1.Challenge
