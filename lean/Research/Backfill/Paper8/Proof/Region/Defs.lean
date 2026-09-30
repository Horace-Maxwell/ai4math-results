import Batteries.Data.List.Basic

/-!
# Region search: computable definitions (agent `region`)

Definitions evaluated by the kernel for Lemma 5.4 and Proposition 5.5 of paper 8. A *support*
is a sublist `Bl` of `[0, 1, …, 12]` (the set `B`); a *tree* is a list `T = [(b₁, k₁), …]` of
branch sizes with their multiplicities. `choices Bl b` lists the multiplicities of `b` allowed by
the two conditions of Lemma 5.4 (with `|ℒ_b(k)|` in the closed form `Lof b k` of Lemma 4.1),
`evalR T t` is `R(t)`, and `checkTree T` is the test applied to every tree of the region.
Their meaning is proved in `Research.Backfill.Paper8.Proof.Region.Enum`, `Research.Backfill.Paper8.Proof.Region.Bridge` and `Research.Backfill.Paper8.Proof.Region.Crit`.
-/

set_option autoImplicit false

namespace P8Region

/-- `|ℒ_β(k)|` in closed form (Lemma 4.1), for `β, k ≥ 1`. -/
def Lof (β k : Nat) : Nat :=
  if β = 1 then (if k = 1 then 2 else k - 1)
  else k * β - 1 - (if β = 2 ∧ k = 2 then 1 else 0)

/-- The largest element of a list (`0` for the empty list): `b*` of a support. -/
def bsOf (Bl : List Nat) : Nat := Bl.foldr max 0

/-- `sq(B, b*)`: the number of `q ≥ 1` with `q² ≤ b* − 1` and `q² ∉ B`. -/
def sqC (Bl : List Nat) (bs : Nat) : Nat :=
  ((List.range' 1 bs).filter (fun q => q ^ 2 ≤ bs - 1 ∧ q ^ 2 ∉ Bl)).length

/-- `ν(B)`. -/
def nuC (Bl : List Nat) : Nat := min (sqC Bl (bsOf Bl) + 1) Bl.length

/-- `M(B)`. -/
def MC (Bl : List Nat) : Nat := 2 * nuC Bl + (Bl.length - nuC Bl) / 2

/-- The multiplicities `k ≥ 1` of `b` allowed in the region for the support `Bl`:
`2(k + 1) ≤ 3ν + r` for `b = 0`, and `|ℒ_b(k)| ≤ M` for `b ≥ 1` (then `k ≤ M + 1`). -/
def choices (Bl : List Nat) (b : Nat) : List Nat :=
  if b = 0 then List.range' 1 ((3 * nuC Bl + Bl.length) / 2 - 1)
  else (List.range' 1 (MC Bl + 1)).filter (fun k => Lof b k ≤ MC Bl)

/-- All trees `[(b, k_b) : b ∈ rest]` with `k_b ∈ choices Bl b`. -/
def treesAux (Bl : List Nat) : List Nat → List (List (Nat × Nat))
  | [] => [[]]
  | b :: rest => (choices Bl b).flatMap (fun k => (treesAux Bl rest).map (fun T => (b, k) :: T))

/-- The trees of the region with support `Bl`. -/
def treesOf (Bl : List Nat) : List (List (Nat × Nat)) := treesAux Bl Bl

/-- The supports `B ⊆ {0, …, 12}` with `b* ≥ 2`. -/
def supports : List (List Nat) := (List.range 13).sublists.filter (fun Bl => 2 ≤ bsOf Bl)

/-- The trees of the supports with indices `lo, …, lo + len − 1`. -/
def chunk (lo len : Nat) : List (List (Nat × Nat)) := ((supports.drop lo).take len).flatMap treesOf

/-- One step of the evaluation of `(∏ (t − b), ∑ k_b ∏_{b' ≠ b} (t − b'))`. -/
def PSstep (t : Int) (b k : Nat) (x : Int × Int) : Int × Int :=
  ((t - b) * x.1, k * x.1 + (t - b) * x.2)

/-- `(∏_{(b,k) ∈ T} (t − b), ∑_{(b,k) ∈ T} k ∏_{(b',k') ∈ T, b' ≠ b} (t − b'))`. -/
def PS (t : Int) : List (Nat × Nat) → Int × Int
  | [] => (1, 0)
  | p :: T => PSstep t p.1 p.2 (PS t T)

/-- `R(t)` for the tree `T`. -/
def evalR (T : List (Nat × Nat)) (t : Int) : Int := (PS t T).1 - (PS t T).2

/-- The number of branches `k = ∑ k_b`. -/
def sumK (T : List (Nat × Nat)) : Nat := (T.map Prod.snd).sum

/-- `k_b` for the tree `T`. -/
def kOf (T : List (Nat × Nat)) (b : Nat) : Nat := (T.map (fun p => if p.1 = b then p.2 else 0)).sum

/-- An upper bound for `N_I`: the number of `1 ≤ q ≤ 6` with `q² ≤ lim` and `R(q²) = 0`. -/
def NIc (T : List (Nat × Nat)) (lim : Nat) : Nat :=
  ((List.range' 1 6).filter (fun q => q * q ≤ lim ∧ evalR T ((q * q : Nat) : Int) = 0)).length

/-- `true` if the absolute value of the integer is not a perfect square. -/
def notSq (z : Int) : Bool := !((List.range (z.natAbs + 1)).any (fun q => q * q = z.natAbs))

/-- The test of Proposition 5.5: (a′) or (b′) with `N_I ≤ NIc` and `N_I + 2 N_II + N_ei ≤ r`, or,
when `NIc = 0` and `|R(0)|` is not a square, (a′) with `N_I = 0` and `2 N_II < r`. -/
def critT (T : List (Nat × Nat)) : Bool :=
  let r := T.length
  let ni := NIc T (bsOf (T.map Prod.fst) + sumK T)
  (T.any (fun p => 1 ≤ p.1 ∧ 2 * ni + (r - ni) / 2 + 1 ≤ Lof p.1 p.2) ||
    decide (1 ≤ kOf T 0 ∧ 3 * ni + r < 2 * (kOf T 0 + 1))) ||
  (decide (ni = 0) && notSq (evalR T 0) &&
    T.any (fun p => 1 ≤ p.1 ∧ (r - 1) / 2 + 1 ≤ Lof p.1 p.2))

/-- The three exceptions `(2,2)`, `(2,0,0)` and `(3)`. -/
def isExc (T : List (Nat × Nat)) : Bool :=
  decide (T = [(2, 2)] ∨ T = [(0, 2), (2, 1)] ∨ T = [(3, 1)])

/-- The number of vertices `n = 1 + ∑ k_b + ∑ b k_b`. -/
def nOf (T : List (Nat × Nat)) : Nat := 1 + sumK T + (T.map (fun p => p.1 * p.2)).sum

/-- The test applied to every tree of the region. -/
def checkTree (T : List (Nat × Nat)) : Bool :=
  decide (nOf T ≤ 124 ∧ bsOf (T.map Prod.fst) + sumK T ≤ 48) && (critT T || isExc T)

/-- Number of trees and result of the test on a list of trees. -/
def stats (l : List (List (Nat × Nat))) : Nat × Bool := (l.length, l.all checkTree)

end P8Region
