import Research.Backfill.Paper7.LegacyCandidates

/-! Exact mathematical search specification; no C execution is performed.
B2's floating run is deliberately absent: its fixed historical dumps are in
LegacyDumpContracts. Source-to-rule bindings are explicit in SOURCE-BINDINGS.json.
Machine overflow absence and timing are historical observations, not hypotheses.
-/
set_option autoImplicit false
open scoped Classical
noncomputable section
namespace BackfillPaper7.Challenge.Legacy
open Polynomial Finset

/-- B2/B3 here means B versions 2/3 (sunB), never the LAPACK program sunB2. -/
def BReaches (cycleFilter countBound useWindow rotation : Bool)
    (b N : ℕ) (x : PQ b) : Prop :=
  Budget b N x ∧ MomentPass cycleFilter true countBound b N x ∧
  (rotation = true → RotationRule key1000 b x) ∧
  (useWindow = true → ∀ d : ℕ, 1 ≤ d → d ≤ b →
    ∃ s, Admissible cycleFilter b N s ∧
      windowLo d x ≤ targetTheta b s ∧ targetTheta b s ≤ windowHi N d x ∧
      (countBound = true → Even b → PartialCountPass b N d x s))

def CandB3 (b N : ℕ) : Set (PQ b) := {x | BReaches true true true true b N x}

def keySupport (p q : ℕ) : ℕ := (if 0 < p then 1 else 0) + 2*(if 0 < q then 1 else 0)

def PatternPass (rank refined : Bool) (b N : ℕ) (x : PQ b) : Prop :=
  let kp := (Kp b x.1).card
  let kq := (Kq b x.2).card
  let r0 : ℤ := (b : ℤ)+kp-delta0 b x.1
  (rank = true → (sigmaSq (r0 - if kq = 0 then 4 else 0) : ℤ) ≤ 2*N) ∧
  (refined = true →
    if kq = 0 then (sigmaSq (r0-4) : ℤ) ≤ 2*N-4
    else (sigmaSq r0 : ℤ) ≤ 2*N-2*kq)

inductive SearchVersion
  | a4 | a5 | a6 (count : Bool)
  | b1 | b2 | b3
  | c (rank : Bool) | c2 (rank refined : Bool)
  | d1 (canonical : Bool)
  | d2 (canonical cycleFilter weightRotation : Bool)
  | d3 (canonical cycleFilter weightRotation noPruning : Bool)
  deriving DecidableEq

/-- Domains supported by the bound and array sizes of the actual source versions.
A's listed odd runs have b≤15 (integer-power overflow beyond this is not covered).
D3 is the version that handles b=22,26 and odd cycles with no pruning. -/
def RunDomain (v : SearchVersion) (b N : ℕ) : Prop :=
  3 ≤ b ∧ b ≤ N ∧ N ≤ 49 ∧
  match v with
  | .a4 | .a5 | .a6 _ => b ≤ 26 ∧ (Odd b → b ≤ 15)
  | .b1 | .b2 | .b3 => b ≤ 18 ∧ (Odd b → b ≤ 15)
  | .c _ => b ≤ 14
  | .c2 r rr => b ≤ 14 ∧ (rr = true → r = true)
  | .d1 _ | .d2 _ _ _ => Even b ∧ b ≤ 16
  | .d3 _ _ _ np => b ≤ 32 ∧ (np = false → Even b)

/-- All-D-stage predicates retain the version-specific load bound and optional
cycle filter, canonical key and weight-based rotation rule. -/
def DStage (load cycleFilter canonical weightRotation noPruning : Bool)
    (b N : ℕ) (x : PQ b) : Prop :=
  Budget b N x ∧
  (noPruning = false → MomentPass cycleFilter load false b N x) ∧
  (canonical = true → Canonical (if weightRotation then keyWeight else key64)
    weightRotation b x) ∧
  (weightRotation = true → RotationRule (fun p q => p+2*q) b x)

def Stage (v : SearchVersion) (b N : ℕ) (x : PQ b) : Prop :=
  match v with
  | .a4 => AReaches false false b N x
  | .a5 => AReaches true false b N x
  | .a6 c => AReaches true c b N x
  | .b1 => x ∈ CandB1 b N ∧ Canonical key1000 false b x
  | .b2 => BReaches true false true false b N x ∧ Canonical key1000 false b x
  | .b3 => BReaches true true true true b N x ∧ Canonical key1000 true b x
  | .c r => Budget b N x ∧ PatternPass r false b N x ∧ Canonical keySupport false b x
  | .c2 r rr => Budget b N x ∧ PatternPass r rr b N x ∧ Canonical keySupport false b x
  | .d1 c => DStage false false c false false b N x
  | .d2 c l w => DStage true l c w false b N x
  | .d3 c l w np => DStage true l c w np b N x

/-- Full budget recursion, not a list of claimed solutions. It enumerates all
labelled tuples and is the common finite specification below the search rules. -/
def enumerateRows : ℕ → ℕ → List (List (ℕ × ℕ))
  | 0, _ => [[]]
  | r+1, W => (List.range (W+1)).flatMap fun p =>
      (List.range ((W-p)/2+1)).flatMap fun q =>
        (enumerateRows r (W-p-2*q)).map (fun tail => (p,q)::tail)

def rowPQ (b : ℕ) (row : List (ℕ × ℕ)) : PQ b :=
  (fun i => (row.getD i.val (0,0)).1, fun i => (row.getD i.val (0,0)).2)

def Enumerated (b N : ℕ) : Set (PQ b) :=
  {x | ∃ row ∈ enumerateRows b (N-b), row.length = b ∧ rowPQ b row = x ∧ 0 < weight x}

def LeafSet (v : SearchVersion) (b N : ℕ) : Set (PQ b) :=
  {x | x ∈ Enumerated b N ∧ Stage v b N x}

/-- Independent integer factorization certificate for a positive output. Neither
modular survival nor IsIntegralGraph is used as the definition of certification. -/
def IntegerFactorCertificate (b : ℕ) (x : PQ b) : Prop :=
  ∃ roots : List ℤ, ((SG b x.1 x.2).adjMatrix ℤ).charpoly =
    (roots.map (fun z => (X - C z : Polynomial ℤ))).prod

def CertifiedOutputs (v : SearchVersion) (b N : ℕ) : Set (PQ b) :=
  {x | x ∈ LeafSet v b N ∧ IntegerFactorCertificate b x}

def FeatureDominates (b : ℕ) (s t : SpectralCounts) : Prop :=
  m4 b s ≤ m4 b t ∧ s2 b s ≤ s2 b t ∧
    ∀ m : ℕ, 1 ≤ m → m ≤ 9 → specGT b s m ≤ specGT b t m ∧ specGE b s m ≤ specGE b t m

def ParetoMaximal (cycleFilter : Bool) (b N : ℕ) (s : SpectralCounts) : Prop :=
  Admissible cycleFilter b N s ∧ ∀ t, Admissible cycleFilter b N t →
    FeatureDominates b s t → FeatureDominates b t s

/-- Exact rules for mathematical pruning, including every prefix and zero case.
No correctness premise about the search, the DP table or a numerical oracle occurs. -/
def PruningAndEnumerationCompleteness : Prop :=
  (∀ cyc b N s, Admissible cyc b N s →
    ∃ t, ParetoMaximal cyc b N t ∧ FeatureDominates b s t) ∧
  (∀ b N : ℕ, b ≤ N → Enumerated b N = {x | Budget b N x}) ∧
  (∀ b N : ℕ, 3 ≤ b → b ≤ N → N ≤ 49 → ∀ x, Budget b N x →
    IsIntegralGraph (SG b x.1 x.2) →
    ∃ s, AdmissibleBase b N s ∧
      (∀ i : Fin 8, (s.1 i).val = mult (SG b x.1 x.2) (value i)) ∧
      (Odd b → ∀ i : Fin 8, (s.2 i).val = mult (SG b x.1 x.2) (-(value i : ℝ)))) ∧
  (∀ b N d : ℕ, 3 ≤ b → d < b → N ≤ 49 →
    ∀ x y : PQ b, (∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i) →
    ∀ cyc cnt : Bool, AMonotonePass cyc cnt b N d y → AMonotonePass cyc cnt b N d x) ∧
  (∀ b N d : ℕ, 3 ≤ b → d ≤ b → N ≤ 49 → ∀ x, Budget b N x →
    IsIntegralGraph (SG b x.1 x.2) → WindowPass true b N d x) ∧
  (∀ r w t : ℕ, t < 3072 →
    (reachD1 r w t ↔ ∃ x : PQ r, weight x = w ∧ theta x = t)) ∧
  (∀ r w Q t : ℕ, t < 3072 →
    (reachD2 r w Q t ↔ ∃ x : PQ r, weight x = w ∧ qSum x = Q ∧ theta x = t)) ∧
  (∀ load cyc : Bool, ∀ b N d : ℕ, 3 ≤ b → Even b → b ≤ N → N ≤ 49 → d ≤ b →
    ∀ x : PQ b, weight («prefix» d x) ≤ N-b →
    (DReachable load cyc b N (b-d) (weight («prefix» d x))
      (qSum («prefix» d x)) (prefixTheta d x).toNat ↔
      ∃ y : PQ b, b + weight y ≤ N ∧ «prefix» d y = «prefix» d x ∧ MomentPass cyc load false b N y)) ∧
  (∀ v b N, RunDomain v b N → ∀ x : PQ b, Budget b N x → IsIntegralGraph (SG b x.1 x.2) →
    ∃ σ : Fin b → Fin b, IsDihedral b σ ∧ reindex σ x ∈ LeafSet v b N) ∧
  (∀ v b N, RunDomain v b N → ∀ x : PQ b,
    (x ∈ CertifiedOutputs v b N ↔ x ∈ LeafSet v b N ∧ IsIntegralGraph (SG b x.1 x.2))) ∧
  (∀ v b N, RunDomain v b N → ∀ x : PQ b, Budget b N x →
    (IsIntegralGraph (SG b x.1 x.2) ↔
      ∃ σ : Fin b → Fin b, IsDihedral b σ ∧ reindex σ x ∈ CertifiedOutputs v b N))

/-- Further zero cells: B version3 includes count/window guards; C's zero at
b13 concerns its rank-pruned canonical support enumeration. -/
def LegacyPruningEmptyCells : Prop :=
  CandB3 14 42 = ∅ ∧ CandB3 18 42 = ∅ ∧
  LeafSet (.c true) 13 41 = ∅

end BackfillPaper7.Challenge.Legacy
