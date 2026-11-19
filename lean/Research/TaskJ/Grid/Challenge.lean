import Mathlib.Data.Nat.Dist
import Mathlib.Data.List.Perm.Basic

/-!
# Yuan's longest open traversal of a rectangular grid

A positive list of side lengths specifies a finite product, with coordinates
numbered from zero. An ordering lists every vertex once and may take steps of
any Manhattan length. The bound in Yuan's equation (6) is interpreted in the
integers, including when the grid contains just one point.
-/

namespace Challenge

abbrev Point := List ℕ

/-- Cartesian product of the ranges of the side lengths, in coordinate order. -/
def vertices : List ℕ → List Point
  | [] => [[]]
  | d :: ds => (List.range d).flatMap fun x => (vertices ds).map (x :: ·)

/-- An arbitrary bijective listing of the box vertices. -/
def Order (ds : List ℕ) (p : List Point) : Prop := p.Perm (vertices ds)

def manhattan (x y : Point) : ℕ := (List.zipWith Nat.dist x y).sum

/-- Distances between consecutive vertices only; both endpoints are free. -/
def pathLength : List Point → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: rest => manhattan x y + pathLength (y :: rest)

def PositiveSides (ds : List ℕ) : Prop := ∀ d ∈ ds, 0 < d

/-- Literal signed coordinate summand from Yuan (6), with multiplicity N/d. -/
def rawTerm (N d : ℕ) : ℤ :=
  ((N / d * (d ^ 2 / 2) : ℕ) : ℤ) -
    (if d % 2 = 0 then 1 else 0) -
    (if N / d = 1 ∧ d % 2 = 1 then 1 else 0)

def rawUpper (ds : List ℕ) : ℤ := (ds.map (rawTerm ds.prod)).sum

def activeCount (ds : List ℕ) : ℕ := (ds.filter (fun d => 1 < d)).length

def evenCount (ds : List ℕ) : ℕ := (ds.filter (fun d => d % 2 = 0)).length

/-- Closed formula for the signed difference between (6) and the true maximum.
For a singleton box, the literal (6) contributes -1 per nominal axis. -/
def gapFormula (ds : List ℕ) : ℤ :=
  match activeCount ds with
  | 0 => -(ds.length : ℤ)
  | 1 => 0
  | 2 =>
    if evenCount ds = 1 ∧ (∃ d ∈ ds, d % 2 = 0 ∧ 4 ≤ d) then 0 else 1
  | _ + 3 =>
    if evenCount ds = 0 then 1 else (2 : ℤ) ^ (evenCount ds - 1) - 1

def optimumFormula (ds : List ℕ) : ℤ := rawUpper ds - gapFormula ds

def IsLongest (ds : List ℕ) (p : List Point) : Prop :=
  Order ds p ∧ ∀ q, Order ds q → pathLength q ≤ pathLength p

/-- Uniform upper bound, including all positive degenerate and narrow grids. -/
def LengthUpperBound : Prop :=
  ∀ ds, PositiveSides ds → ∀ p, Order ds p → (pathLength p : ℤ) ≤ optimumFormula ds

/-- A Hamiltonian ordering that attains the claimed value for each grid. -/
def LengthAttained : Prop :=
  ∀ ds, PositiveSides ds → ∃ p, Order ds p ∧ (pathLength p : ℤ) = optimumFormula ds

/-- The signed gap at every maximizing ordering, as in the question in §6.3. -/
def YuanGapAtLongest : Prop :=
  ∀ ds, PositiveSides ds → ∀ p, IsLongest ds p → rawUpper ds - (pathLength p : ℤ) = gapFormula ds

end Challenge
