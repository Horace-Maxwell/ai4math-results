import Research.Backfill.Paper7.AlgebraicContracts
import Research.Backfill.Paper7.LegacyDumpContracts
import Research.Backfill.Paper7.LegacyTransfer

/-! New unproved expected test types, numbered after V2's 074--102.
These are requirements, not passing tests or paper proofs. -/
set_option autoImplicit false
open scoped Classical
noncomputable section
namespace BackfillPaper7.Challenge.LegacyTests
open BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy
open BackfillPaper7.Challenge.Legacy.Algebra
open Polynomial

/-- Empty LEAF rows must not be padded and silently accepted. -/
def test_103_required : Prop := parseLeaf "LEAF 0,0" = none
/-- Invalid numeric tokens must remain a parse failure. -/
def test_104_required : Prop := parsePair "a,2" = none
/-- The exact ten-column zero row parses; whether to exclude bare cycles is a separate predicate. -/
def test_105_required : Prop :=
  parseLeaf "LEAF 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0 0,0" = some (0,0)

def test_106_required : Prop := ¬ Budget 4 49 (0,0)
def test_107_required : Prop := ¬ AdmissibleBase 4 41 (0,0)
def test_108_required : Prop :=
  ¬ RotationRule key1000 3 (![0,1,0], ![0,0,0]) ∧
  RotationRule key1000 3 (![1,0,0], ![0,0,0])
/-- Least and greatest canonical representatives have genuinely different meanings. -/
def test_109_required : Prop :=
  Canonical key1000 false 3 (![0,0,1], ![0,0,0]) ∧
  ¬ Canonical key1000 true 3 (![0,0,1], ![0,0,0])

def test_110_required : Prop := reachD1 0 0 0 ∧ ¬ reachD1 0 1 0
def test_111_required : Prop := reachD2 1 2 1 8 ∧ ¬ reachD2 1 2 0 8
/-- The finite-storage cutoff is part of the old recurrence, not an unbounded table. -/
def test_112_required : Prop := ¬ reachD1 1 0 3072

def test_113_required : Prop := freeQ 4 ![10,10,0,0] = 18
/-- A b by b nullity without the free-arm term cannot bound multiplicity 19. -/
def test_114_required : Prop :=
  mult (SG 4 ![0,0,0,0] ![10,10,0,0]) 1 = 19 ∧
  ¬ mult (SG 4 ![0,0,0,0] ![10,10,0,0]) 1 ≤ 4
/-- Bad reduction may strictly increase nullity. -/
def test_115_required : Prop :=
  matrixNullity (overQ (!![7] : Matrix (Fin 1) (Fin 1) ℤ)) = 0 ∧
  matrixNullity (overMod 7 (!![7] : Matrix (Fin 1) (Fin 1) ℤ)) = 1
/-- A prime alone does not ensure distinct residues in a wide integer window. -/
def test_116_required : Prop := (9 : ZMod 17) = (-8 : ZMod 17)
/-- Modular splitting does not imply integer splitting. -/
def test_117_required : Prop :=
  modularRootSum 7 (integerWindow 3) (X^2-2) = 2 ∧
  ¬ IntegerFactorizationOn (X^2-2) (integerWindow 3)
/-- For a bare triangle, F has degree 12 and includes the artificial 0/±1 factors. -/
def test_118_required : Prop :=
  clearedF 3 (0 : Fin 3 → ℕ) (0 : Fin 3 → ℕ) =
    X^3*(X^2-1)^3*(X^3-3*X-2)

def test_119_required : Prop := chainPolynomial [] = 1
/-- Order of transfer factors is not commuted. -/
def test_120_required : Prop :=
  integerMono (![1,2,3], ![0,0,0]) 2 =
    integerTk (![1,2,3], ![0,0,0]) 2 2 *
    integerTk (![1,2,3], ![0,0,0]) 2 1 *
    integerTk (![1,2,3], ![0,0,0]) 2 0

end BackfillPaper7.Challenge.LegacyTests
