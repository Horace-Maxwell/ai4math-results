import Mathlib

/-!
# Distance eigenvalues of connected cographs below `-2`

Statement file for Open Problem "Distance eigenvalues of cographs below -2 and sharpness", part (i),
of Manna, Mandal and Tura, *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*,
arXiv:2611.06981v1 (4 November 2026):

> Is there `ε > 0` such that `(-2-ε, -2)` contains no distance eigenvalue of any connected cograph?

`OpenProblemI_negative` says that the answer is no.

Definitions follow the survey: a cograph is a finite simple graph with no induced path on four
vertices; the distance matrix of a connected graph is `D(G) = (d(u,v))_{u,v}`.
-/

set_option autoImplicit false

namespace CographDist

/-- `G` has an induced path on four vertices: four distinct vertices `f 0, f 1, f 2, f 3` such
that `f i` and `f j` are adjacent exactly when `|i - j| = 1`. -/
def HasInducedP4 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : Fin 4 → V, Function.Injective f ∧
    ∀ i j : Fin 4, G.Adj (f i) (f j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)

/-- A cograph: a simple graph with no induced `P₄`. -/
def IsCograph {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ HasInducedP4 G

/-- The distance matrix `D(G) = (d(u,v))_{u,v}` over `ℝ`, with Mathlib's graph distance.
(Mathlib's `dist` is `0` for unreachable pairs; this file uses it only for connected graphs.) -/
noncomputable def distMatrix {V : Type*} (G : SimpleGraph V) : Matrix V V ℝ :=
  fun u v => (G.dist u v : ℝ)

/-- `μ` is a (real) distance eigenvalue of `G`: `D(G) x = μ x` for some nonzero real vector `x`. -/
def IsDistEigenvalue {V : Type*} [Fintype V] (G : SimpleGraph V) (μ : ℝ) : Prop :=
  ∃ x : V → ℝ, x ≠ 0 ∧ (distMatrix G).mulVec x = μ • x

/-- The answer to part (i) is no: for every `ε > 0` some finite connected cograph has a distance
eigenvalue in the open interval `(-2-ε, -2)`. -/
def OpenProblemI_negative : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    G.Connected ∧ IsCograph G ∧ ∃ μ : ℝ, -2 - ε < μ ∧ μ < -2 ∧ IsDistEigenvalue G μ

end CographDist
