import Research.Backfill.Paper7.ChallengeV2

/-!
Exact mathematical specifications extracted from the legacy sources bound in
SOURCE-BINDINGS.json. This file contains definitions and unproved contracts only.
`AReaches` uses exact real inertia (the mathematical meaning of the rational
pivot recurrence), not floating arithmetic. B2/LAPACK is not modeled here: its
actual dumps are separate finite data objects, with no completeness assumption.
-/
set_option autoImplicit false
open scoped Classical
noncomputable section
namespace BackfillPaper7.Challenge.Legacy
open Finset

abbrev PQ (b : ℕ) := (Fin b → ℕ) × (Fin b → ℕ)
abbrev Counts := Fin 8 → Fin 3
abbrev SpectralCounts := Counts × Counts

def value (i : Fin 8) : ℕ := i.val + 2

def pSum {b : ℕ} (x : PQ b) : ℕ := ∑ i, x.1 i
def qSum {b : ℕ} (x : PQ b) : ℕ := ∑ i, x.2 i
def weight {b : ℕ} (x : PQ b) : ℕ := pSum x + 2 * qSum x
def theta {b : ℕ} (x : PQ b) : ℤ := ∑ i, thetaV (x.1 i) (x.2 i)
def Budget (b N : ℕ) (x : PQ b) : Prop := 0 < weight x ∧ b + weight x ≤ N

def posCard (s : SpectralCounts) : ℕ := ∑ i, (s.1 i).val
def negCard (s : SpectralCounts) : ℕ := ∑ i, (s.2 i).val

def s2 (b : ℕ) (s : SpectralCounts) : ℤ :=
  ∑ i, ((s.1 i).val + if Even b then 0 else (s.2 i).val : ℕ) * (value i : ℤ)^2

def m4 (b : ℕ) (s : SpectralCounts) : ℤ :=
  ∑ i, ((s.1 i).val + if Even b then 0 else (s.2 i).val : ℕ) *
    (value i : ℤ)^2 * ((value i : ℤ)^2 - 1)

def cyclicPositive (b : ℕ) : ℕ :=
  ((Finset.range b).filter (fun j => 6 * min j (b-j) < b)).card

def cyclicNegative (b : ℕ) : ℕ :=
  ((Finset.range b).filter (fun j => 3 * |2 * (j : ℤ) - (b : ℤ)| < b)).card

/-- A4/B1 enumerate the same unreduced feature family. For even b the negative
vector is fixed to zero because S2 and M4 count only the positive half. -/
def AdmissibleBase (b N : ℕ) (s : SpectralCounts) : Prop :=
  (∃ ρ : Fin 8, 3 ≤ value ρ ∧ s.1 ρ = 1 ∧
    (∀ i, value ρ < value i → s.1 i = 0) ∧
    (if Even b then s.2 = 0 else ∀ i, value ρ ≤ value i → s.2 i = 0)) ∧
  s2 b s ≤ (if Even b then (N : ℤ) else 2 * N) ∧
  (Odd b → ∀ L : ℕ, Odd L → 3 ≤ L → L ≤ b →
    (∑ i, ((s.1 i).val - (s.2 i).val : ℤ) * ((value i : ℤ)^L - value i)) =
      if L = b then 2 * b else 0)

/-- cycleFilter is enabled by A5/A6, B2/B3; not by A4/B1/D1/D2 default. -/
def Admissible (cycleFilter : Bool) (b N : ℕ) (s : SpectralCounts) : Prop :=
  AdmissibleBase b N s ∧
  (cycleFilter = true → cyclicPositive b ≤ posCard s ∧
    (Odd b → cyclicNegative b ≤ negCard s))

def targetTheta (b : ℕ) (s : SpectralCounts) : ℤ :=
  if Even b then m4 b s - (if b = 4 then 4 else 0) else m4 b s / 2

def specGT (b : ℕ) (s : SpectralCounts) (m : ℕ) : ℕ :=
  let a := ∑ i ∈ Finset.univ.filter (fun i => m < value i), (s.1 i).val
  let c := ∑ i ∈ Finset.univ.filter (fun i => m < value i), (s.2 i).val
  if Even b then a else min a c

def specGE (b : ℕ) (s : SpectralCounts) (m : ℕ) : ℕ :=
  if m < 2 then 0 else
  let a := ∑ i ∈ Finset.univ.filter (fun i => m ≤ value i), (s.1 i).val
  let c := ∑ i ∈ Finset.univ.filter (fun i => m ≤ value i), (s.2 i).val
  if Even b then a else min a c

/-- All subtractions are in Z: low bounds may be negative. -/
def MomentPass (cycleFilter loadBound countBound : Bool) (b N : ℕ) (x : PQ b) : Prop :=
  ∃ s, Admissible cycleFilter b N s ∧
    m4 b s = (if Even b then theta x + (if b = 4 then 4 else 0) else 2 * theta x) ∧
    s2 b s ≤ (if Even b then (b + weight x : ℤ) else 2 * (b + weight x)) ∧
    (loadBound = true →
      (if Even b then (b + weight x : ℤ) - max (qSum x) 2
       else 2 * (b + weight x : ℤ) - 2 * max (qSum x) 2) ≤ s2 b s) ∧
    (countBound = true → Even b →
      0 ≤ 2 * s2 b s - (b + weight x) - 2 * posCard s ∧
      2 * s2 b s - (b + weight x) - 2 * posCard s ≤ max (pSum x) 2)

def «prefix» {b : ℕ} (d : ℕ) (x : PQ b) : PQ b :=
  (fun i => if i.val < d then x.1 i else 0,
   fun i => if i.val < d then x.2 i else 0)

/-- Assigned contribution: bare unassigned vertices are not included. -/
def prefixTheta {b : ℕ} (d : ℕ) (x : PQ b) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin b => i.val < d), thetaV (x.1 i) (x.2 i)

def windowLo {b : ℕ} (d : ℕ) (x : PQ b) : ℤ := prefixTheta d x + 2 * ((b : ℤ)-d)
def windowHi {b : ℕ} (N d : ℕ) (x : PQ b) : ℤ :=
  let rem : ℤ := N - (b : ℤ) - weight («prefix» d x)
  prefixTheta d x + if d < b then (2+rem)*(1+rem)+2*((b : ℤ)-d-1) else 0

def WindowPass (cycleFilter : Bool) (b N d : ℕ) (x : PQ b) : Prop :=
  ∃ s, Admissible cycleFilter b N s ∧
    windowLo d x ≤ targetTheta b s ∧ targetTheta b s ≤ windowHi N d x

abbrev PathIndex (b : ℕ) := {i : Fin b // i.val < b-1}
abbrev RIndex (b d : ℕ) (x : PQ b) :=
  {i : Fin b // i.val < b-1 ∧ («prefix» d x).2 i = 0}

def pathMatrix (b d : ℕ) (x : PQ b) (m : ℝ) :
    Matrix (PathIndex b) (PathIndex b) ℝ := fun i j =>
  if i = j then fk b («prefix» d x).1 («prefix» d x).2 m i.val - m
  else if i.val.val + 1 = j.val.val ∨ j.val.val + 1 = i.val.val then 1 else 0

def rPathMatrix (b d : ℕ) (x : PQ b) : Matrix (RIndex b d x) (RIndex b d x) ℝ := fun i j =>
  if i = j then ((«prefix» d x).1 i.val : ℝ) - 1
  else if i.val.val + 1 = j.val.val ∨ j.val.val + 1 = i.val.val then 1 else 0

def lowerGT (b d : ℕ) (x : PQ b) (m : ℕ) : ℕ :=
  if m = 1 then (Kq b («prefix» d x).2).card + nPos (rPathMatrix b d x)
  else nPos (pathMatrix b d x m)

def lowerGE (b d : ℕ) (x : PQ b) (m : ℕ) : ℕ :=
  if m < 2 then 0 else nPos (pathMatrix b d x m) + nZero (pathMatrix b d x m)

/-- A6 counting guard. Its nmax is integral, not truncated natural subtraction. -/
def PartialCountPass (b N d : ℕ) (x : PQ b) (s : SpectralCounts) : Prop :=
  let nmin : ℤ := max (b + weight («prefix» d x) : ℤ) (s2 b s)
  let nmax : ℤ := min (N : ℤ) (2*s2 b s - 2*posCard s)
  nmin ≤ nmax ∧ (2 ≤ pSum («prefix» d x) →
    2*(qSum («prefix» d x) : ℤ) ≤ 2*nmax-b-2*s2 b s+2*posCard s)

/-- This guard is monotone. The separately defined WindowPass is not used for break. -/
def AMonotonePass (cycleFilter countBound : Bool) (b N d : ℕ) (x : PQ b) : Prop :=
  ∃ s, Admissible cycleFilter b N s ∧
    (if Even b then windowLo d x else 2 * windowLo d x) ≤ m4 b s ∧
    (if Even b then (b : ℤ) + pSum («prefix» d x) + qSum («prefix» d x) - 2
     else 2*((b : ℤ) + pSum («prefix» d x) + qSum («prefix» d x) - 2)) ≤ s2 b s ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ 9 → lowerGT b d x m ≤ specGT b s m ∧ lowerGE b d x m ≤ specGE b s m) ∧
    (countBound = true → Even b → PartialCountPass b N d x s)

def key1000 (p q : ℕ) : ℕ := 1000*p+q
def key64 (p q : ℕ) : ℕ := 64*p+q
def keyWeight (p q : ℕ) : ℕ := 64*(p+2*q)+p

def RotationRule (key : ℕ → ℕ → ℕ) (b : ℕ) (x : PQ b) : Prop :=
  ∀ i j : Fin b, j.val = 0 → key (x.1 i) (x.2 i) ≤ key (x.1 j) (x.2 j)

def LexLE (key : ℕ → ℕ → ℕ) {b : ℕ} (x y : PQ b) : Prop :=
  ∀ i : Fin b, (∀ j : Fin b, j.val < i.val → key (x.1 j) (x.2 j) = key (y.1 j) (y.2 j)) →
    key (x.1 i) (x.2 i) ≤ key (y.1 i) (y.2 i)

def reindex {b : ℕ} (σ : Fin b → Fin b) (x : PQ b) : PQ b := (x.1 ∘ σ, x.2 ∘ σ)

def Canonical (key : ℕ → ℕ → ℕ) (greatest : Bool) (b : ℕ) (x : PQ b) : Prop :=
  ∀ σ, IsDihedral b σ → if greatest then LexLE key (reindex σ x) x else LexLE key x (reindex σ x)

def AReaches (cycleFilter countBound : Bool) (b N : ℕ) (x : PQ b) : Prop :=
  Budget b N x ∧ RotationRule key1000 b x ∧ MomentPass cycleFilter true false b N x ∧
    ∀ d : ℕ, 1 ≤ d → d < b →
      AMonotonePass cycleFilter countBound b N d x ∧ WindowPass cycleFilter b N d x

def CandA4 (b N : ℕ) : Set (PQ b) := {x | AReaches false false b N x}
def CandB1 (b N : ℕ) : Set (PQ b) := {x | Budget b N x ∧ MomentPass false true false b N x}
def CandD1 (b N : ℕ) : Set (PQ b) := {x | Budget b N x ∧ Even b ∧ MomentPass false false false b N x}
def CandD2 (b N : ℕ) : Set (PQ b) := {x | Budget b N x ∧ Even b ∧ MomentPass false true false b N x}

def canonB1 (b N : ℕ) : Set (PQ b) := {x | x ∈ CandB1 b N ∧ Canonical key1000 false b x}
def canonD2 (b N : ℕ) : Set (PQ b) := {x | x ∈ CandD2 b N ∧ Canonical keyWeight true b x}

/-- Full D1 recurrence; finite storage truncation is explicit at 3072. -/
def reachD1 : ℕ → ℕ → ℕ → Prop
  | 0, w, t => w = 0 ∧ t = 0
  | r+1, w, t => t < 3072 ∧ ∃ p q : ℕ, p+2*q ≤ w ∧
      ∃ u : ℕ, (thetaV p q : ℤ) + u = t ∧ reachD1 r (w-p-2*q) u

/-- D2 and D3 track the total number Q of length-two arms. -/
def reachD2 : ℕ → ℕ → ℕ → ℕ → Prop
  | 0, w, Q, t => w = 0 ∧ Q = 0 ∧ t = 0
  | r+1, w, Q, t => t < 3072 ∧ ∃ p q : ℕ, p+2*q ≤ w ∧ q ≤ Q ∧
      ∃ u : ℕ, (thetaV p q : ℤ) + u = t ∧ reachD2 r (w-p-2*q) (Q-q) u

/-- Mathematical F tables of the source, with its exact cutoff and load switch. -/
def DReachable (loadBound cycleFilter : Bool) (b N r W Qu t : ℕ) : Prop :=
  t < 3072 ∧ ∃ s, Admissible cycleFilter b N s ∧ Even b ∧
    ∃ wr Qr tr : ℕ, W+wr ≤ N-b ∧ Qr ≤ (N-b)/2 ∧
      (if loadBound then reachD2 r wr Qr tr else reachD1 r wr tr) ∧
      (t : ℤ) + tr = targetTheta b s ∧ s2 b s ≤ b+W+wr ∧
      (loadBound = true → (b+W+wr : ℤ) ≤ s2 b s + max (Qu+Qr) 2)

/-- Mathematical Table-1 emptiness cells, with versions kept separate.
A6's count option changes guards, not its generated feature set (A5's cycle filter). -/
def LegacySpectrumEmptyCells : Prop :=
  (∀ b ∈ ({5,7,9} : Finset ℕ), {s | Admissible false b 41 s} = ∅) ∧
  (∀ b ∈ ({11,13,15} : Finset ℕ), {s | Admissible false b 41 s} = ∅) ∧
  (∀ b ∈ ({5,7,9} : Finset ℕ), {s | Admissible false b 42 s} = ∅) ∧
  (∀ b ∈ ({5,7,9,11,13,15} : Finset ℕ),
    {s | Admissible false b 42 s} = ∅ ∧ {s | Admissible true b 42 s} = ∅) ∧
  (∀ b ∈ ({22,26} : Finset ℕ), {s | Admissible true b 42 s} = ∅ ∧
    ¬ DReachable true false b 42 b 0 0 0)

/-- D/B prose gives their own counts, not equality of their canonical sets. -/
def LegacyMomentCounts : Prop :=
  (CandB1 4 41).Finite ∧ (CandB1 4 41).ncard = 410544 ∧
  (canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641 ∧
  (CandD2 4 41).Finite ∧ (CandD2 4 41).ncard = 410544 ∧
  (canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641 ∧
  (CandB1 6 42).Finite ∧ (CandB1 6 42).ncard = 14215675 ∧
  (canonB1 6 42).Finite ∧ (canonB1 6 42).ncard = 1187991 ∧
  (CandD2 6 42).Finite ∧ (CandD2 6 42).ncard = 14215675 ∧
  (canonD2 6 42).Finite ∧ (canonD2 6 42).ncard = 1187991

end BackfillPaper7.Challenge.Legacy
