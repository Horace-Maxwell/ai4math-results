import Research.Backfill.Paper7.ChallengeV2

/-!
# Paper 7 V3: additional algebraic statement contracts (source only)

These are unproved proposition definitions, not accepted results. No original
ChallengeV2 definition is replaced. The legacy implementations and their hashes
are bound in ALGEBRA-NOTES.md. Mathematical exactness and machine-code refinement
are different obligations; the latter is not silently asserted here.
-/

set_option autoImplicit false

namespace BackfillPaper7.Challenge.Legacy.Algebra

open Polynomial Finset SimpleGraph
open scoped Classical

noncomputable section

/-! ## Explicit graph and polynomial objects -/

def totalP (b : ℕ) (p : Fin b → ℕ) : ℕ := ∑ k, p k
def totalQ (b : ℕ) (q : Fin b → ℕ) : ℕ := ∑ k, q k

def cycleAdjZ (b : ℕ) : Matrix (Fin b) (Fin b) ℤ :=
  (SimpleGraph.cycleGraph b).adjMatrix ℤ

/-- The characteristic polynomial of the actual adjacency matrix. -/
def graphPhi {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Polynomial ℤ := (G.adjMatrix ℤ).charpoly

/-- Delete vertices, with the remaining vertex type a subtype and all induced edges retained. -/
def deleteVertices {V : Type} (G : SimpleGraph V) (D : Set V) : SimpleGraph {v : V // v ∉ D} :=
  G.induce Dᶜ

def sunCycleVertices (b : ℕ) (L : Fin b → List ℕ) : Set (SunV b L) :=
  Set.range (Sum.inl : Fin b → SunV b L)

/-- Delete the actual undirected cycle edge between the two supplied cycle vertices. -/
def sunDeleteEdge (b : ℕ) (L : Fin b → List ℕ) (u v : Fin b) :
    SimpleGraph (SunV b L) :=
  (sunGraph b L).deleteEdges ({s(Sum.inl u, Sum.inl v)} : Set (Sym2 (SunV b L)))

def clearedMatrix (b : ℕ) (p q : Fin b → ℕ) :
    Matrix (Fin b) (Fin b) (Polynomial ℤ) := fun i j =>
  X * (X ^ 2 - 1) * ((if i = j then X else 0) - C (cycleAdjZ b i j)) -
    (if i = j then C (p i : ℤ) * (X ^ 2 - 1) + C (q i : ℤ) * X ^ 2 else 0)

def clearedF (b : ℕ) (p q : Fin b → ℕ) : Polynomial ℤ :=
  (clearedMatrix b p q).det

/-- MIN-02. All exponents are nonnegative; no truncated subtraction encodes a rational identity. -/
def ClearedCharacteristicPolynomial : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b →
    X ^ totalP b p * (X ^ 2 - 1) ^ totalQ b q * clearedF b p q =
      X ^ b * (X ^ 2 - 1) ^ b * graphPhi (SG b p q) ∧
    (clearedF b p q).Monic ∧ (clearedF b p q).natDegree = 4 * b

/-- MIN-03, general unicyclic form. The cycle is an actual closed walk, and the
deleted cycle vertices are precisely its support. The edge must lie on that cycle. -/
def UnicyclicSchwenkIdentity : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (b : ℕ), IsUnicyclicWithCycle G b →
    ∀ (r : V) (w : G.Walk r r), w.IsCycle → w.length = b →
    ∀ u v : V, s(u, v) ∈ w.edges →
      graphPhi G = graphPhi (G.deleteEdges ({s(u, v)} : Set (Sym2 V))) -
        graphPhi (deleteVertices G ({u, v} : Set V)) -
        2 * graphPhi (deleteVertices G {z | z ∈ w.support})

/-- The sun instance uses the original graph construction, not a placeholder matrix.
The relation on u,v identifies the cycle edge, also when b = 3. -/
def SunSchwenkIdentity : Prop :=
  ∀ (b : ℕ) (L : Fin b → List ℕ), 3 ≤ b → ∀ u v : Fin b,
    (SimpleGraph.cycleGraph b).Adj u v →
      graphPhi (sunGraph b L) = graphPhi (sunDeleteEdge b L u v) -
        graphPhi (deleteVertices (sunGraph b L)
          ({Sum.inl u, Sum.inl v} : Set (SunV b L))) -
        2 * graphPhi (deleteVertices (sunGraph b L) (sunCycleVertices b L))

/-! ## C/C2's polynomial recurrence, attached to the real deletion graphs -/

def legPolynomial (p q : ℕ) : Polynomial ℤ := X ^ p * (X ^ 2 - 1) ^ q

def rootedLegPolynomial (p q : ℕ) : Polynomial ℤ :=
  X * legPolynomial p q -
    (if p = 0 then 0 else C (p : ℤ) * X ^ (p - 1) * (X ^ 2 - 1) ^ q) -
    (if q = 0 then 0 else C (q : ℤ) * X ^ (p + 1) * (X ^ 2 - 1) ^ (q - 1))

/-- State (A,B); exactly A' = R*A - L*B and B' = L*A. -/
def chainStep (state : Polynomial ℤ × Polynomial ℤ) (a : ℕ × ℕ) :
    Polynomial ℤ × Polynomial ℤ :=
  (rootedLegPolynomial a.1 a.2 * state.1 - legPolynomial a.1 a.2 * state.2,
    legPolynomial a.1 a.2 * state.1)

def chainPolynomial (a : List (ℕ × ℕ)) : Polynomial ℤ :=
  (a.foldl chainStep (1, 0)).1

def vertexPairs (b : ℕ) (p q : Fin b → ℕ) : List (ℕ × ℕ) :=
  (List.finRange b).map (fun k => (p k, q k))

/-- The empty chain has polynomial 1. Endpoint deletion retains all their detached
arms; deleting the whole cycle retains all P1 and P2 components. -/
def SchwenkRecurrenceExactness : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b → ∀ u v : Fin b,
    u.val = 0 → v.val + 1 = b →
      graphPhi (sunDeleteEdge b (pq b p q) u v) =
        chainPolynomial (vertexPairs b p q) ∧
      graphPhi (deleteVertices (SG b p q)
        ({Sum.inl u, Sum.inl v} : Set (SunV b (pq b p q)))) =
        legPolynomial (p u) (q u) * legPolynomial (p v) (q v) *
          chainPolynomial (((vertexPairs b p q).drop 1).dropLast) ∧
      graphPhi (deleteVertices (SG b p q) (sunCycleVertices b (pq b p q))) =
        ∏ k, legPolynomial (p k) (q k)

/-! ## Actual modular parameters and non-colliding root windows -/

def bPrimes : Finset ℕ := {1000000007, 998244353, 2305843009213693951}
def cPrimes : Finset ℕ := {2305843009213693951, 1000000000000000003}
def dPrime : ℕ := 2147483647

def integerWindow (R : ℕ) : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)

def reducePolynomial (ℓ : ℕ) (f : Polynomial ℤ) : Polynomial (ZMod ℓ) :=
  f.map (Int.castRingHom (ZMod ℓ))

def modularRootSum (ℓ : ℕ) (S : Finset ℤ) (f : Polynomial ℤ) : ℕ :=
  ∑ m ∈ S, Polynomial.rootMultiplicity (m : ZMod ℓ) (reducePolynomial ℓ f)

/-- A concrete factorization over integers, with an independently supplied allowed set.
This does not redefine integrality of a graph or any rejection conclusion. -/
def IntegerFactorizationOn (f : Polynomial ℤ) (S : Finset ℤ) : Prop :=
  ∃ a : List ℤ, (∀ z ∈ a, z ∈ S) ∧ f = (a.map (fun z => X - C z)).prod

def LegacyModuliAndWindows : Prop :=
  (∀ ℓ ∈ bPrimes ∪ cPrimes ∪ {dPrime}, ℓ.Prime ∧ 216 < ℓ) ∧
  (∀ (ℓ : ℕ) (R : ℕ), ℓ.Prime → 2 * R < ℓ →
    Set.InjOn (fun z : ℤ => (z : ZMod ℓ)) (integerWindow R : Set ℤ))

/-- Generic reduction theorem: all conclusions are to be proved from monicity,
integer factorization and injectivity of the root residues. Only rejection is used. -/
def ModularPolynomialRejectSound : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ (f : Polynomial ℤ) (S : Finset ℤ), f.Monic →
    Set.InjOn (fun z : ℤ => (z : ZMod ℓ)) (S : Set ℤ) →
      (reducePolynomial ℓ f).Monic ∧
      (reducePolynomial ℓ f).natDegree = f.natDegree ∧
      (∀ z : ℤ, Polynomial.rootMultiplicity z f ≤
        Polynomial.rootMultiplicity (z : ZMod ℓ) (reducePolynomial ℓ f)) ∧
      (IntegerFactorizationOn f S → modularRootSum ℓ S f = f.natDegree) ∧
      (modularRootSum ℓ S f < f.natDegree → ¬ IntegerFactorizationOn f S)

/-- The analytic spectral range and the integral factorization bridge, including F's
possible additional roots 0 and ±1, are conclusions, not hypotheses. -/
def SunSpectralWindowAndFactorization : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b → nOf b p q ≤ 49 →
    (∀ x ∈ spec (SG b p q), x ^ 2 ≤ 2 * (nOf b p q : ℝ) ∧ |x| < 10) ∧
    (IsIntegralGraph (SG b p q) →
      IntegerFactorizationOn (graphPhi (SG b p q)) (integerWindow 9) ∧
      IntegerFactorizationOn (clearedF b p q) (integerWindow 9))

/-- The exact rejection directions of B/B2 and C/C2. Passing either sieve is not
asserted to imply integrality. C's larger [-10,10] window is preserved. -/
def LegacyPolynomialSieveSoundness : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b → nOf b p q ≤ 49 →
    (∀ ℓ ∈ bPrimes,
      (IsIntegralGraph (SG b p q) →
        modularRootSum ℓ (integerWindow 9) (clearedF b p q) = 4 * b) ∧
      (modularRootSum ℓ (integerWindow 9) (clearedF b p q) < 4 * b →
        ¬ IsIntegralGraph (SG b p q))) ∧
    (∀ ℓ ∈ cPrimes,
      (IsIntegralGraph (SG b p q) →
        modularRootSum ℓ (integerWindow 10) (graphPhi (SG b p q)) = nOf b p q) ∧
      (modularRootSum ℓ (integerWindow 10) (graphPhi (SG b p q)) < nOf b p q →
        ¬ IsIntegralGraph (SG b p q)))

/-! ## B's 4b+1 sample points, divided differences, and reconstruction -/

def interpolationNode (ℓ : ℕ) (i : ℕ) : ZMod ℓ := (i + 20 : ℕ)

def determinantSample (ℓ b : ℕ) (p q : Fin b → ℕ) (i : ℕ) : ZMod ℓ :=
  ((clearedMatrix b p q).map
    (fun f => (reducePolynomial ℓ f).eval (interpolationNode ℓ i))).det

/-- Divided difference with right endpoint i. When j ≤ i this is the in-place
descending update dd[i] ← (dd[i]-dd[i-1])/(xs[i]-xs[i-j]) of B. -/
def dividedDifference (ℓ : ℕ) [Fact ℓ.Prime] (values : ℕ → ZMod ℓ) :
    ℕ → ℕ → ZMod ℓ
  | 0, i => values i
  | j + 1, i =>
      (dividedDifference ℓ values j i - dividedDifference ℓ values j (i - 1)) /
        (interpolationNode ℓ i - interpolationNode ℓ (i - (j + 1)))

def newtonReconstruction (ℓ : ℕ) [Fact ℓ.Prime] (d : ℕ) (values : ℕ → ZMod ℓ) :
    Polynomial (ZMod ℓ) :=
  ∑ j ∈ Finset.range (d + 1), C (dividedDifference ℓ values j j) *
    ∏ i ∈ Finset.range j, (X - C (interpolationNode ℓ i))

/-- Generic uniqueness plus the actual Newton recurrence, followed by the precise B
determinant sampling specialization. Mathematical field arithmetic is explicit. -/
def ModularInterpolationExactness : Prop :=
  (∀ (ℓ : ℕ) [Fact ℓ.Prime] (d : ℕ), d < ℓ →
    Set.InjOn (interpolationNode ℓ) (Finset.range (d + 1) : Set ℕ) ∧
    (∀ f : Polynomial (ZMod ℓ), f.natDegree ≤ d →
      newtonReconstruction ℓ d (fun i => f.eval (interpolationNode ℓ i)) = f) ∧
    (∀ f g : Polynomial (ZMod ℓ), f.natDegree ≤ d → g.natDegree ≤ d →
      (∀ i ∈ Finset.range (d + 1), f.eval (interpolationNode ℓ i) =
        g.eval (interpolationNode ℓ i)) → f = g)) ∧
  (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∈ bPrimes →
    ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b → b ≤ 49 →
      (∀ i : ℕ, determinantSample ℓ b p q i =
        (reducePolynomial ℓ (clearedF b p q)).eval (interpolationNode ℓ i)) ∧
      newtonReconstruction ℓ (4 * b) (determinantSample ℓ b p q) =
        reducePolynomial ℓ (clearedF b p q))

/-! ## Rank, nullity, exceptional eigenvalues, and the integral spectral sum -/

def matrixNullity {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) : ℕ :=
  Module.finrank K (LinearMap.ker (Matrix.toLin' M))

def overQ {n : Type} (M : Matrix n n ℤ) : Matrix n n ℚ := M.map (fun z => (z : ℚ))
def overR {n : Type} (M : Matrix n n ℤ) : Matrix n n ℝ := M.map (fun z => (z : ℝ))
def overMod {n : Type} (ℓ : ℕ) (M : Matrix n n ℤ) : Matrix n n (ZMod ℓ) :=
  M.map (fun z => (z : ZMod ℓ))

def RankReductionAndNullity : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (M : Matrix n n ℤ)
    (ℓ : ℕ), ℓ.Prime →
      (overMod ℓ M).rank ≤ (overQ M).rank ∧
      matrixNullity (overQ M) ≤ matrixNullity (overMod ℓ M) ∧
      (overQ M).rank = (overR M).rank ∧
      matrixNullity (overQ M) = matrixNullity (overR M) ∧
      (overMod ℓ M).rank + matrixNullity (overMod ℓ M) = Fintype.card n ∧
      (overQ M).rank + matrixNullity (overQ M) = Fintype.card n

/-- Complete real spectrum, rational eigenspace multiplicities, and the integer
factorization of charpoly are explicitly connected to the original graph predicate. -/
def SpectrumMultiplicityBridge : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj],
      (spec G).card = Fintype.card V ∧
      (∀ m : ℤ, mult G (m : ℝ) =
        matrixNullity (overQ ((G.adjMatrix ℤ) - m • (1 : Matrix V V ℤ)))) ∧
      (IsIntegralGraph G ↔ ∃ S : Finset ℤ, IntegerFactorizationOn (graphPhi G) S) ∧
      (∀ S : Finset ℤ, IsIntegralGraph G →
        (∀ x ∈ spec G, ∃ m ∈ S, x = (m : ℝ)) →
        ∑ m ∈ S, mult G (m : ℝ) = Fintype.card V)

def scaledSchur (b : ℕ) (p q : Fin b → ℕ) (m : ℤ) : Matrix (Fin b) (Fin b) ℤ :=
  (m * (m ^ 2 - 1)) • (cycleAdjZ b - m • (1 : Matrix (Fin b) (Fin b) ℤ)) +
    Matrix.diagonal (fun k => (p k : ℤ) * (m ^ 2 - 1) + (q k : ℤ) * m ^ 2)

def zeroSystem (b : ℕ) (p : Fin b → ℕ) : Matrix (Fin b) (Fin b) ℤ := fun k j =>
  if 0 < p k then (if j = k then 1 else 0) else cycleAdjZ b k j

def signSystem (b : ℕ) (p q : Fin b → ℕ) (ε : ℤ) :
    Matrix (Fin b) (Fin b) ℤ := fun k j =>
  if 0 < q k then (if j = k then 1 else 0)
  else cycleAdjZ b k j + if j = k then ε * ((p k : ℤ) - 1) else 0

/-- This sum, including only nonempty bundles, is the number of free arm parameters. -/
def freeP (b : ℕ) (p : Fin b → ℕ) : ℕ := ∑ k ∈ Kp b p, (p k - 1)
def freeQ (b : ℕ) (q : Fin b → ℕ) : ℕ := ∑ k ∈ Kq b q, (q k - 1)

/-- Exact characteristic-zero formulas, including offsets at all exceptional values. -/
def ReducedMultiplicityExactness : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b →
    freeP b p + (Kp b p).card = totalP b p ∧
    freeQ b q + (Kq b q).card = totalQ b q ∧
    freeP b p = totalP b p - (Kp b p).card ∧
    freeQ b q = totalQ b q - (Kq b q).card ∧
    (∀ m : ℤ, m ≠ -1 → m ≠ 0 → m ≠ 1 →
      mult (SG b p q) (m : ℝ) = matrixNullity (overQ (scaledSchur b p q m))) ∧
    mult (SG b p q) 0 = freeP b p + matrixNullity (overQ (zeroSystem b p)) ∧
    (∀ ε : ℤ, ε = 1 ∨ ε = -1 →
      mult (SG b p q) (ε : ℝ) =
        freeQ b q + matrixNullity (overQ (signSystem b p q ε)))

def modularMultiplicityBound (ℓ b : ℕ) (p q : Fin b → ℕ) (m : ℤ) : ℕ :=
  if m = 0 then freeP b p + matrixNullity (overMod ℓ (zeroSystem b p))
  else if m = 1 ∨ m = -1 then
    freeQ b q + matrixNullity (overMod ℓ (signSystem b p q m))
  else matrixNullity (overMod ℓ (scaledSchur b p q m))

/-- MIN-05. Includes every integer m, without assuming the Schur scalar remains
nonzero modulo ℓ. A zero scalar can loosen the bound but cannot justify rejection. -/
def ModularNullityUpperBounds : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b →
    ∀ m : ℤ, mult (SG b p q) (m : ℝ) ≤ modularMultiplicityBound ℓ b p q m

def IntegralMultiplicitySum : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b → nOf b p q ≤ 49 →
    IsIntegralGraph (SG b p q) →
      ∑ m ∈ integerWindow 9, mult (SG b p q) (m : ℝ) = nOf b p q

/-- The fixed D/D2/D3 sieve. The sum includes the free-arm offsets at 0 and ±1. -/
def LegacyNullitySieveSoundness : Prop :=
  ∀ (b : ℕ) (p q : Fin b → ℕ), 3 ≤ b → nOf b p q ≤ 49 →
    (IsIntegralGraph (SG b p q) →
      nOf b p q ≤ ∑ m ∈ integerWindow 9, modularMultiplicityBound dPrime b p q m) ∧
    ((∑ m ∈ integerWindow 9, modularMultiplicityBound dPrime b p q m) < nOf b p q →
      ¬ IsIntegralGraph (SG b p q))

end

end BackfillPaper7.Challenge.Legacy.Algebra
