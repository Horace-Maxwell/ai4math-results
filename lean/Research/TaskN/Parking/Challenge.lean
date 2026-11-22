import Mathlib

namespace TaskN.Parking.Challenge

open scoped Classical

/-- All coordinates below use offsets: street spot 1 has offset 0.
A gap (l,r) is the half-open vacant interval [l,r). Between the finite gaps
and the frontier all spots are occupied. Every spot from the frontier on is free. -/
abbrev Street := List (ℕ × ℕ) × ℕ

/-- Place a car of length len at the first run of vacant spots beginning at
or after pref. Gaps are searched left to right. An infinite free tail lets
us check the original street boundary on the final frontier. -/
def park (pref len : ℕ) : List (ℕ × ℕ) → ℕ → Street
  | [], frontier =>
      if pref ≤ frontier then ([], frontier + len)
      else ([(frontier, pref)], pref + len)
  | (l,r) :: gaps, frontier =>
      let start := max l pref
      if start + len ≤ r then
        ((if l < start then [(l,start)] else []) ++
         (if start + len < r then [(start + len,r)] else []) ++ gaps, frontier)
      else
        let after := park pref len gaps frontier
        ((l,r) :: after.1, after.2)

/-- Arrival list entries are (car length, preferred offset). -/
def drive (street : Street) (arrivals : List (ℕ × ℕ)) : Street :=
  arrivals.foldl (fun state car => park car.2 car.1 state.1 state.2) street

def ordinary (lengths : List ℕ) : List (ℕ × ℕ) :=
  lengths.map (fun len => (len,0))

/-- All rearrangements of a list with one distinguished preference are obtained
by giving that preference to one arrival and preference 1 to every other car. -/
def allPositions (lengths : List ℕ) (offset : ℕ) : Prop :=
  ∀ (before : List ℕ) (len : ℕ) (after : List ℕ), lengths = before ++ len :: after →
    (drive ([],0) (ordinary before ++ (len,offset) :: ordinary after)).2 ≤ lengths.sum

/-- Chen's W uses positive one-based spot numbers up to the street length.
The offset 0, when admissible, is recorded as the preference 1. -/
noncomputable def W (lengths : List ℕ) : Finset ℕ :=
  ((Finset.range lengths.sum).filter (allPositions lengths)).image Nat.succ

def positive (lengths : List ℕ) : Prop := ∀ x ∈ lengths, 0 < x

def subsetSums : List ℕ → Finset ℕ
  | [] => {0}
  | x :: xs => subsetSums xs ∪ (subsetSums xs).image (fun s => x+s)

def dominant : List ℕ → Prop
  | [] => True
  | x :: xs => xs.sum < x ∧ dominant xs

/-- The sorted prefix of the subset sums ending at z is symmetric about z/2. -/
def prefixSymmetric (xs : List ℕ) (z : ℕ) : Prop :=
  z ∈ subsetSums xs ∧ ∀ s ∈ subsetSums xs, s ≤ z → z-s ∈ subsetSums xs

def extremeLengths : List ℕ → Prop
  | [] => False
  | [_] => True
  | a :: b :: xs =>
      b ≤ a ∧ dominant (b :: xs) ∧
      (xs.sum ≤ a-b ∨ prefixSymmetric xs (xs.sum - (a-b)))

/-- Spacings in low-to-high order. The input is in arrival order (large to small
when dominant), and each spacing subtracts the sum of all later car lengths. -/
def jumps : List ℕ → List ℕ
  | [] => []
  | x :: xs => jumps xs ++ [x-xs.sum]

/-- Each pair is the common value and length of a maximal constant run. -/
def runs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | x :: xs =>
      match runs xs with
      | [] => [(x,1)]
      | (y,k) :: rest => if x = y then (y,k+1) :: rest else (x,1) :: (y,k) :: rest

def runContribution (spacings : List ℕ) : ℕ :=
  ((runs spacings).map (fun entry => 2^entry.2 - 1)).sum

/-- Theorem E(b)'s upper bound and the full characterization of its equality cases. -/
def ExtremalClassification : Prop :=
  ∀ (lengths : List ℕ), lengths ≠ [] → positive lengths →
    (W lengths).card ≤ 2^(lengths.length-1) ∧
    ((W lengths).card = 2^(lengths.length-1) ↔ extremeLengths lengths)

/-- Number of first-car lengths attaining equality in the inclusive band
[b,b+sum tail] for any tail obeying the necessary superincreasing condition. -/
def FirstLengthCount : Prop :=
  ∀ (b : ℕ) (xs : List ℕ), dominant (b :: xs) →
    ((Finset.Icc b (b + xs.sum)).filter
      (fun a => (W (a :: b :: xs)).card = 2^((b :: xs).length))).card =
      1 + runContribution (jumps xs)

end TaskN.Parking.Challenge
