import Research.WordRepTensor.Proof.WRWords
import Research.WordRepTensor.Proof.WRGraphs

/-!
# Finite window checks for the Mycielskians of odd cycles

Data for the local argument that rules out word-representations of `mu (2k+1)` and
`muExt (2k+1)` (written by Claude, 2026-09-28). The data were produced by
`work/claude-lean/wordrep/gen/gen_window.py`, which is not trusted: every property of them that
the proof uses is proved in Lean. The finite checks (`patValid`, `flipOK`, `noneOK`) are
`decide +kernel` proofs in `WRWindow`; that the edge lists and patterns describe the graphs is
proved in `WRMycielski` by `fin_cases` and `decide`, and the shift of the state edges by `rfl`.
The counts in the `--` comments below are generator output, not Lean theorems.

Window labels: `0` the root, `1, 2, 3` the top vertices `v i, v (i+1), v (i+2)`, `4, 5, 6` the
shadows `u i, u (i+1), u (i+2)`. For `mu 3` the labels are the root, `v 0, v 1, v 2` and
`u 0, u 1, u 2`. An orientation of an edge list `E` is a function `o : ℕ → Bool`; `o e = true`
orients the `e`-th edge `(x, y)` from `x` to `y`. A *pattern* is a directed path `a → c → d → b`
along three edges, with `a ~ b` and a missing chord `a ~ d` or `c ~ b`; `cond3B o P` says that no
pattern of `P` is oriented along `o`.
-/

set_option autoImplicit false

namespace ClaudeWordRep

structure Pat where
  a : Fin 7
  c : Fin 7
  d : Fin 7
  b : Fin 7
  e1 : ℕ
  d1 : Bool
  e2 : ℕ
  d2 : Bool
  e3 : ℕ
  d3 : Bool
deriving DecidableEq

-- window of mu: 9 edges, 16 bad 3-paths (generator output, not a Lean theorem)
def winMuEdges : List (Fin 7 × Fin 7) := [(1, 2), (2, 3), (4, 2), (5, 1), (5, 3), (6, 2), (0, 4), (0, 5), (0, 6)]
def winMuPats : List Pat := [⟨1, 2, 3, 5, 0, true, 1, true, 4, false⟩,
    ⟨2, 1, 5, 3, 0, false, 3, false, 4, true⟩,
    ⟨2, 3, 5, 1, 1, true, 4, false, 3, true⟩,
    ⟨3, 2, 1, 5, 1, false, 0, false, 3, false⟩,
    ⟨4, 2, 6, 0, 2, true, 5, false, 8, false⟩,
    ⟨2, 4, 0, 6, 2, false, 6, false, 8, true⟩,
    ⟨5, 1, 2, 3, 3, true, 0, true, 1, true⟩,
    ⟨1, 5, 3, 2, 3, false, 4, true, 1, false⟩,
    ⟨5, 3, 2, 1, 4, true, 1, false, 0, false⟩,
    ⟨3, 5, 1, 2, 4, false, 3, true, 0, true⟩,
    ⟨6, 2, 4, 0, 5, true, 2, false, 6, false⟩,
    ⟨2, 6, 0, 4, 5, false, 8, false, 6, true⟩,
    ⟨0, 4, 2, 6, 6, true, 2, true, 5, false⟩,
    ⟨4, 0, 6, 2, 6, false, 8, true, 5, true⟩,
    ⟨0, 6, 2, 4, 8, true, 5, true, 2, false⟩,
    ⟨6, 0, 4, 2, 8, false, 6, true, 2, true⟩]
def winMuS0 : List (ℕ × Bool) := [(6, true), (7, true), (0, true), (3, false), (2, true)]
def winMuS1 : List (ℕ × Bool) := [(7, true), (8, true), (1, true), (5, false), (4, true)]
def winMuCol : List Bool := [false, true, false, false, false, false, false, false, true, true, false, true, false, true, false, false, true, true, false, true, false, true, false, false, true, true, true, true, true, true, false, true]

-- window of mu': 11 edges, 32 bad 3-paths (generator output, not a Lean theorem)
def winExtEdges : List (Fin 7 × Fin 7) := [(1, 2), (2, 3), (4, 2), (5, 1), (5, 3), (6, 2), (0, 4), (0, 5), (0, 6), (4, 3), (6, 1)]
def winExtPats : List Pat := [⟨1, 2, 3, 5, 0, true, 1, true, 4, false⟩,
    ⟨2, 1, 5, 3, 0, false, 3, false, 4, true⟩,
    ⟨2, 3, 5, 1, 1, true, 4, false, 3, true⟩,
    ⟨3, 2, 1, 5, 1, false, 0, false, 3, false⟩,
    ⟨4, 2, 6, 0, 2, true, 5, false, 8, false⟩,
    ⟨2, 4, 0, 6, 2, false, 6, false, 8, true⟩,
    ⟨5, 1, 2, 3, 3, true, 0, true, 1, true⟩,
    ⟨5, 1, 6, 0, 3, true, 10, false, 8, false⟩,
    ⟨1, 5, 3, 2, 3, false, 4, true, 1, false⟩,
    ⟨1, 5, 0, 6, 3, false, 7, false, 8, true⟩,
    ⟨5, 3, 2, 1, 4, true, 1, false, 0, false⟩,
    ⟨5, 3, 4, 0, 4, true, 9, false, 6, false⟩,
    ⟨3, 5, 1, 2, 4, false, 3, true, 0, true⟩,
    ⟨3, 5, 0, 4, 4, false, 7, false, 6, true⟩,
    ⟨6, 2, 4, 0, 5, true, 2, false, 6, false⟩,
    ⟨2, 6, 0, 4, 5, false, 8, false, 6, true⟩,
    ⟨0, 4, 2, 6, 6, true, 2, true, 5, false⟩,
    ⟨0, 4, 3, 5, 6, true, 9, true, 4, false⟩,
    ⟨4, 0, 5, 3, 6, false, 7, true, 4, true⟩,
    ⟨4, 0, 6, 2, 6, false, 8, true, 5, true⟩,
    ⟨0, 5, 1, 6, 7, true, 3, true, 10, false⟩,
    ⟨0, 5, 3, 4, 7, true, 4, true, 9, false⟩,
    ⟨5, 0, 4, 3, 7, false, 6, true, 9, true⟩,
    ⟨5, 0, 6, 1, 7, false, 8, true, 10, true⟩,
    ⟨0, 6, 2, 4, 8, true, 5, true, 2, false⟩,
    ⟨0, 6, 1, 5, 8, true, 10, true, 3, false⟩,
    ⟨6, 0, 4, 2, 8, false, 6, true, 2, true⟩,
    ⟨6, 0, 5, 1, 8, false, 7, true, 3, true⟩,
    ⟨4, 3, 5, 0, 9, true, 4, false, 7, false⟩,
    ⟨3, 4, 0, 5, 9, false, 6, false, 7, true⟩,
    ⟨6, 1, 5, 0, 10, true, 3, false, 7, false⟩,
    ⟨1, 6, 0, 5, 10, false, 8, false, 7, true⟩]
def winExtS0 : List (ℕ × Bool) := [(6, true), (7, true), (0, true), (3, false), (2, true)]
def winExtS1 : List (ℕ × Bool) := [(7, true), (8, true), (1, true), (5, false), (4, true)]
def winExtCol : List Bool := [false, true, false, false, false, false, false, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, true, true, true, false, false, true]

-- mu_3: 12 edges, 48 bad 3-paths (generator output); `mu3_none` checks that no orientation passes
def mu3Edges : List (Fin 7 × Fin 7) := [(1, 2), (2, 3), (3, 1), (4, 2), (4, 3), (5, 1), (5, 3), (6, 1), (6, 2), (0, 4), (0, 5), (0, 6)]
def mu3Pats : List Pat := [⟨1, 2, 3, 5, 0, true, 1, true, 6, false⟩,
    ⟨1, 2, 4, 3, 0, true, 3, false, 4, true⟩,
    ⟨2, 1, 3, 4, 0, false, 2, false, 4, false⟩,
    ⟨2, 1, 5, 3, 0, false, 5, false, 6, true⟩,
    ⟨2, 3, 1, 6, 1, true, 2, true, 7, false⟩,
    ⟨2, 3, 5, 1, 1, true, 6, false, 5, true⟩,
    ⟨3, 2, 1, 5, 1, false, 0, false, 5, false⟩,
    ⟨3, 2, 6, 1, 1, false, 8, false, 7, true⟩,
    ⟨3, 1, 2, 4, 2, true, 0, true, 3, false⟩,
    ⟨3, 1, 6, 2, 2, true, 7, false, 8, true⟩,
    ⟨1, 3, 2, 6, 2, false, 1, false, 8, false⟩,
    ⟨1, 3, 4, 2, 2, false, 4, false, 3, true⟩,
    ⟨4, 2, 1, 3, 3, true, 0, false, 2, false⟩,
    ⟨4, 2, 6, 0, 3, true, 8, false, 11, false⟩,
    ⟨2, 4, 3, 1, 3, false, 4, true, 2, true⟩,
    ⟨2, 4, 0, 6, 3, false, 9, false, 11, true⟩,
    ⟨4, 3, 1, 2, 4, true, 2, true, 0, true⟩,
    ⟨4, 3, 5, 0, 4, true, 6, false, 10, false⟩,
    ⟨3, 4, 2, 1, 4, false, 3, true, 0, false⟩,
    ⟨3, 4, 0, 5, 4, false, 9, false, 10, true⟩,
    ⟨5, 1, 2, 3, 5, true, 0, true, 1, true⟩,
    ⟨5, 1, 6, 0, 5, true, 7, false, 11, false⟩,
    ⟨1, 5, 3, 2, 5, false, 6, true, 1, false⟩,
    ⟨1, 5, 0, 6, 5, false, 10, false, 11, true⟩,
    ⟨5, 3, 2, 1, 6, true, 1, false, 0, false⟩,
    ⟨5, 3, 4, 0, 6, true, 4, false, 9, false⟩,
    ⟨3, 5, 1, 2, 6, false, 5, true, 0, true⟩,
    ⟨3, 5, 0, 4, 6, false, 10, false, 9, true⟩,
    ⟨6, 1, 3, 2, 7, true, 2, false, 1, false⟩,
    ⟨6, 1, 5, 0, 7, true, 5, false, 10, false⟩,
    ⟨1, 6, 2, 3, 7, false, 8, true, 1, true⟩,
    ⟨1, 6, 0, 5, 7, false, 11, false, 10, true⟩,
    ⟨6, 2, 3, 1, 8, true, 1, true, 2, true⟩,
    ⟨6, 2, 4, 0, 8, true, 3, false, 9, false⟩,
    ⟨2, 6, 1, 3, 8, false, 7, true, 2, false⟩,
    ⟨2, 6, 0, 4, 8, false, 11, false, 9, true⟩,
    ⟨0, 4, 2, 6, 9, true, 3, true, 8, false⟩,
    ⟨0, 4, 3, 5, 9, true, 4, true, 6, false⟩,
    ⟨4, 0, 5, 3, 9, false, 10, true, 6, true⟩,
    ⟨4, 0, 6, 2, 9, false, 11, true, 8, true⟩,
    ⟨0, 5, 1, 6, 10, true, 5, true, 7, false⟩,
    ⟨0, 5, 3, 4, 10, true, 6, true, 4, false⟩,
    ⟨5, 0, 4, 3, 10, false, 9, true, 4, true⟩,
    ⟨5, 0, 6, 1, 10, false, 11, true, 7, true⟩,
    ⟨0, 6, 1, 5, 11, true, 7, true, 5, false⟩,
    ⟨0, 6, 2, 4, 11, true, 8, true, 3, false⟩,
    ⟨6, 0, 4, 2, 11, false, 9, true, 3, true⟩,
    ⟨6, 0, 5, 1, 11, false, 10, true, 5, true⟩]

end ClaudeWordRep
