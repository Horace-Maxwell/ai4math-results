import Research.Backfill.Paper7.LegacyEnumeration

/-! MIN-06. Integer transfer matrices and the actual A-run CRT domain.
The original double/log2 guard is not a premise. Every magnitude bound below
is an unproved integer theorem obligation on an explicitly enumerated leaf set.
-/
set_option autoImplicit false
open scoped Classical
noncomputable section
namespace BackfillPaper7.Challenge.Legacy
open Finset

def aPrimes : List ℕ :=
  [4611686018427387847, 4611686018427387817, 4611686018427387787, 4611686018427387761]

def transferH (m : ℤ) : ℤ := m*(m^2-1)

def transferS {b : ℕ} (x : PQ b) (m : ℤ) (k : Fin b) : ℤ :=
  m^2*(m^2-1) - (x.1 k : ℤ)*(m^2-1) - (x.2 k : ℤ)*m^2

def integerTk {b : ℕ} (x : PQ b) (m : ℤ) (k : Fin b) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![transferS x m k, -transferH m; transferH m, 0]

/-- Multiplication order is T_(b-1) ... T_0, exactly the M <- T*M loop. -/
def integerMono {b : ℕ} (x : PQ b) (m : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  ((List.finRange b).reverse.map (integerTk x m)).prod

/-- Infinity-row-norm product. No floating logarithm occurs. -/
def rowEnvelope {b : ℕ} (x : PQ b) (m : ℤ) : ℕ :=
  ∏ k, ((transferS x m k).natAbs + (transferH m).natAbs)

def traceDifference {b : ℕ} (x : PQ b) (m : ℤ) : ℤ :=
  (integerMono x m).trace - 2*(transferH m)^b

def scalarDifference {b : ℕ} (x : PQ b) (m : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  integerMono x m - (transferH m)^b • (1 : Matrix (Fin 2) (Fin 2) ℤ)

/-- Explicit finite run family named in the paper; no universal b≤N≤49 bound is
smuggled into the magnitude claim. A6's count flag is part of the version. -/
def ReportedARun (v : SearchVersion) (b N : ℕ) : Prop :=
  (v = .a4 ∧ (b,N) ∈ ({(3,41),(4,41),(5,41),(7,41),(8,41),(9,41),(10,41),(12,41),
      (3,42),(5,42),(6,42),(7,42),(9,42),(3,49)} : Finset (ℕ × ℕ))) ∨
  (v = .a5 ∧ (b,N) ∈ ({(10,42),(14,42),(18,42)} : Finset (ℕ × ℕ))) ∨
  (v = .a6 true ∧ (b,N) ∈ ({(6,42),(10,42),(22,42),(26,42),(4,49)} : Finset (ℕ × ℕ))) ∨
  (v = .a6 false ∧ b = 4 ∧ N = 49)

/-- The exact residues tested by A, before interpreting them as multiplicities. -/
def CRTTraceZero {b : ℕ} (x : PQ b) (m : ℤ) : Prop :=
  ∀ ℓ ∈ aPrimes, (traceDifference x m : ZMod ℓ) = 0

def CRTScalarZero {b : ℕ} (x : PQ b) (m : ℤ) : Prop :=
  ∀ ℓ ∈ aPrimes, ∀ i j : Fin 2, (scalarDifference x m i j : ZMod ℓ) = 0

def CRTMultiplicity {b : ℕ} (x : PQ b) (m : ℤ) : ℕ :=
  if CRTScalarZero x m then 2 else if CRTTraceZero x m then 1 else 0

/-- All standard integer/matrix semantics are conclusions. Neither the double
guard nor correctness of a candidate residue table is an added hypothesis. -/
def LegacyTransferCRTExactness : Prop :=
  (∀ ℓ ∈ aPrimes, ℓ.Prime ∧ ℓ < 2^62) ∧
  aPrimes.Pairwise Nat.Coprime ∧ 2^240 < aPrimes.prod ∧
  (∀ z : ℤ, z.natAbs < aPrimes.prod →
    ((∀ ℓ ∈ aPrimes, (z : ZMod ℓ) = 0) ↔ z = 0)) ∧
  (∀ (b : ℕ) (x : PQ b) (m : ℤ), 2 ≤ m.natAbs →
    (integerMono x m).map (fun z => (z : ℝ)) =
      ((transferH m : ℝ)^b) • Mono b x.1 x.2 (m : ℝ)) ∧
  (∀ (b : ℕ) (x : PQ b) (m : ℤ), 2 ≤ m.natAbs →
    (∀ i j : Fin 2, (integerMono x m i j).natAbs ≤ rowEnvelope x m) ∧
    (traceDifference x m).natAbs ≤ 2*rowEnvelope x m+2*(transferH m).natAbs^b ∧
    (∀ i j : Fin 2, (scalarDifference x m i j).natAbs ≤
      rowEnvelope x m+(transferH m).natAbs^b)) ∧
  (∀ v b N, ReportedARun v b N → ∀ x ∈ LeafSet v b N, ∀ m : ℤ,
    2 ≤ m.natAbs → m.natAbs ≤ 9 →
      2*rowEnvelope x m+2*(transferH m).natAbs^b < 2^240 ∧
      (traceDifference x m).natAbs < 2^240 ∧
      (∀ i j : Fin 2, (scalarDifference x m i j).natAbs < 2^240) ∧
      (CRTTraceZero x m ↔ (integerMono x m).trace = 2*(transferH m)^b) ∧
      (CRTScalarZero x m ↔ integerMono x m = (transferH m)^b • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ∧
      CRTMultiplicity x m = mult (SG b x.1 x.2) (m : ℝ))

end BackfillPaper7.Challenge.Legacy
