import Research.TaskH.Fan.Challenge

/-! The known Gao--Huo--Liu--Ma rooted path theorem, statement only.
Every output path is in the original graph G. The extra root edge only tests connectivity.
This is an auxiliary for Task H, not a new assumption on its frozen Main.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
variable {V : Type u}

/-- A finite, sorted arithmetic progression of lengths of actual simple paths. -/
def AdmissiblePathFamily (G : SimpleGraph V) (x y : V) (k a d : ℕ)
    (p : Fin k → G.Walk x y) : Prop :=
  2 ≤ a ∧ (d = 1 ∨ d = 2) ∧ ∀ i : Fin k, (p i).IsPath ∧ (p i).length = a + i.val * d

/-- Actual G-paths, with their starting length and common difference supplied internally. -/
def HasAdmissiblePaths (G : SimpleGraph V) (x y : V) (k : ℕ) : Prop :=
  ∃ a d : ℕ, ∃ p : Fin k → G.Walk x y, AdmissiblePathFamily G x y k a d p

/-- Published rooted theorem over every positive path count and every finite vertex type. -/
noncomputable def RootedPathClaim : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (x y : V),
    TaskH.Fan.RootedTwoConnected G x y →
      TaskH.Fan.NonrootDegreeAtLeast G x y (k + 1) → HasAdmissiblePaths G x y k

#print axioms AdmissiblePathFamily
#print axioms HasAdmissiblePaths
#print axioms RootedPathClaim
end TaskH.Gao
