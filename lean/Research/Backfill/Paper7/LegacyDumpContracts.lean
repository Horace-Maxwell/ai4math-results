import Research.Backfill.Paper7.LegacyCandidates
import Research.Backfill.Paper7.LegacyDumpA4Part0
import Research.Backfill.Paper7.LegacyDumpA4Part1
import Research.Backfill.Paper7.LegacyDumpB2v1Part0
import Research.Backfill.Paper7.LegacyDumpB2v1Part1
import Research.Backfill.Paper7.LegacyDumpB2v1Part2
import Research.Backfill.Paper7.LegacyDumpB2v1Part3

/-! Fixed finite data assertions are separate from search completeness.
The B2 set below means the six-hash-bound historical dump data, not an idealized
LAPACK implementation. No floating correctness hypothesis is assumed. -/
set_option autoImplicit false
open scoped Classical
noncomputable section
namespace BackfillPaper7.Challenge.Legacy

/-- Header lines and DONE lines are not leaf records. No LEAF row is silently repaired. -/
def leafLines (raw : String) : List String :=
  (raw.splitOn "\n").filter (fun s => s.startsWith "LEAF ")

def parsePair (s : String) : Option (ℕ × ℕ) :=
  match s.splitOn "," with
  | [a,b] => do
      let p ← a.toNat?
      let q ← b.toNat?
      pure (p,q)
  | _ => none

def parseLeaf (s : String) : Option (PQ 10) := do
  match s.splitOn " " with
  | "LEAF" :: fields =>
      if fields.length = 10 then
        let pairs ← fields.mapM parsePair
        pure (fun i => (pairs.getD i.val (0,0)).1,
              fun i => (pairs.getD i.val (0,0)).2)
      else none
  | _ => none

def rawA4 : List String := [Raw.a4Part0, Raw.a4Part1]
def rawB2v1 : List String := [Raw.b2v1Part0, Raw.b2v1Part1, Raw.b2v1Part2, Raw.b2v1Part3]

def dumpRows (raw : List String) : List (PQ 10) := (raw.flatMap leafLines).filterMap parseLeaf

def DumpWellFormed (raw : List String) : Prop :=
  ∀ s ∈ raw.flatMap leafLines, (parseLeaf s).isSome = true

def dumpA4 : Finset (PQ 10) := (dumpRows rawA4).toFinset
def dumpB2v1 : Finset (PQ 10) := (dumpRows rawB2v1).toFinset

/-- The exact set/equality/cardinality claim about the two fixed historical data
objects. No claim that B2's floating DFS is complete is included or assumed. -/
def LegacyDump52652 : Prop :=
  DumpWellFormed rawA4 ∧ DumpWellFormed rawB2v1 ∧
  (dumpRows rawA4).Nodup ∧ (dumpRows rawB2v1).Nodup ∧
  dumpA4 = dumpB2v1 ∧ dumpA4.card = 52652 ∧
  (∀ x ∈ dumpA4, Budget 10 41 x ∧ RotationRule key1000 10 x ∧
    ¬ IsIntegralGraph (SG 10 x.1 x.2))

/-- Separate non-circular bridge: the exact rational mathematical A4 leaf
predicate equals its recorded set. It must be proved, not inferred from a log.
Together with LegacyDump52652 this gives CandA4's exact 52652 cardinality. -/
def LegacyA4DumpCompleteness : Prop :=
  CandA4 10 41 = (dumpA4 : Set (PQ 10)) ∧
  (CandA4 10 41).Finite ∧ (CandA4 10 41).ncard = 52652 ∧
  ∀ x ∈ CandA4 10 41, ¬ IsIntegralGraph (SG 10 x.1 x.2)

end BackfillPaper7.Challenge.Legacy
