import Research.WordRepTensor.Challenge

/-!
# Known-answer tests for the definitions of `Challenge.lean` (wordrep)

Not part of the frozen challenge.  Small `decide` checks that the custom definitions mean what
the sources say, including instances that must come out FALSE.  Edge counts are compared with
[A, Remark 2.1] ("the degree of `(u,v)` equals `deg u · deg v`") and with the independent Python
constructors (`work/round7/wordrep/code/graphs.py`, `logs/target_*.out`: `μ₃ × W₇` has 336 edges).
-/

set_option autoImplicit false

open WordRepTensor.Challenge SimpleGraph

/-! ## Alternation and representation ([A, §1]) -/

example : Alternate [0, 1, 0, 1] (0 : ℕ) 1 := by decide
example : Alternate [0, 2, 1, 2, 0, 1] (0 : ℕ) 1 := by decide      -- other letters are deleted
example : Alternate [1, 0, 1] (0 : ℕ) 1 := by decide               -- odd length, starts with y
example : ¬ Alternate [0, 0, 1] (0 : ℕ) 1 := by decide
example : ¬ Alternate [0, 1, 1, 0] (0 : ℕ) 1 := by decide

-- the 4-cycle 0-1-2-3-0 is represented by 02132031; the word 0123 represents K₄ instead
example : Represents (cycleGraph 4) [0, 2, 1, 3, 2, 0, 3, 1] := by decide
example : ¬ Represents (cycleGraph 4) [0, 1, 2, 3] := by decide
example : Represents (⊤ : SimpleGraph (Fin 3)) [0, 1, 2] := by decide
-- every vertex must occur
example : ¬ Represents (⊥ : SimpleGraph (Fin 2)) [0, 0] := by decide

/-! ## Cycle, wheel, (extended) Mycielskian ([A, §1.1]) -/

example : (cycleGraph 5).Adj 0 4 := by decide
example : ¬ (cycleGraph 5).Adj 0 2 := by decide
example : (wheel 5).Adj (.inr ()) (.inl 3) := by decide
example : (wheel 5).Adj (.inl 4) (.inl 0) := by decide
example : ¬ (wheel 5).Adj (.inl 0) (.inl 2) := by decide
-- top–top, top–shadow (only C_n-neighbours), shadow–root; shadows independent; root ≁ top
example : (mu 5).Adj (.inl 0) (.inl 1) := by decide
example : (mu 5).Adj (.inl 0) (.inr (.inl 1)) := by decide
example : (mu 5).Adj (.inr (.inl 4)) (.inl 0) := by decide
example : ¬ (mu 5).Adj (.inl 0) (.inr (.inl 0)) := by decide
example : ¬ (mu 5).Adj (.inl 0) (.inr (.inl 2)) := by decide
example : (mu 5).Adj (.inr (.inl 2)) (.inr (.inr ())) := by decide
example : ¬ (mu 5).Adj (.inr (.inl 0)) (.inr (.inl 1)) := by decide
example : ¬ (mu 5).Adj (.inl 0) (.inr (.inr ())) := by decide
-- extended: top a ~ shadow b iff a ≠ b
example : (muExt 5).Adj (.inl 0) (.inr (.inl 2)) := by decide
example : ¬ (muExt 5).Adj (.inl 2) (.inr (.inl 2)) := by decide
-- μ'_3 = μ_3 ([A, Fig. 3 caption])
example : ∀ a b, (muExt 3).Adj a b ↔ (mu 3).Adj a b := by decide

/-! ## Edge counts (ordered adjacent pairs = 2 |E|) -/

-- μ_3: 12 edges, μ_5: 20, μ'_5: 30, W_7: 14 ([A, Figs. 1–3]; Python constructors)
example : (Finset.univ.filter (fun p : (Fin 3 ⊕ Fin 3 ⊕ Unit) × (Fin 3 ⊕ Fin 3 ⊕ Unit) =>
    (mu 3).Adj p.1 p.2)).card = 24 := by decide
example : (Finset.univ.filter (fun p : (Fin 5 ⊕ Fin 5 ⊕ Unit) × (Fin 5 ⊕ Fin 5 ⊕ Unit) =>
    (mu 5).Adj p.1 p.2)).card = 40 := by decide
example : (Finset.univ.filter (fun p : (Fin 5 ⊕ Fin 5 ⊕ Unit) × (Fin 5 ⊕ Fin 5 ⊕ Unit) =>
    (muExt 5).Adj p.1 p.2)).card = 60 := by decide
example : (Finset.univ.filter (fun p : (Fin 7 ⊕ Unit) × (Fin 7 ⊕ Unit) =>
    (wheel 7).Adj p.1 p.2)).card = 28 := by decide
-- tensor product: degree of (root, hub) in μ_3 × W_7 is 3 · 7 = 21 ([A, Remark 2.1])
example : (Finset.univ.filter (fun q : (Fin 3 ⊕ Fin 3 ⊕ Unit) × (Fin 7 ⊕ Unit) =>
    (tensorProd (mu 3) (wheel 7)).Adj (.inr (.inr ()), .inr ()) q)).card = 21 := by decide
example : ¬ (tensorProd (mu 3) (wheel 7)).Adj (.inl 0, .inl 0) (.inl 1, .inl 0) := by decide
example : (tensorProd (mu 3) (wheel 7)).Adj (.inl 0, .inl 0) (.inl 1, .inl 6) := by decide

/-! ## Reviewer's extra tests (REVIEW-CHALLENGE.md §4; copied from `review/ReviewerExtraTests.lean`)

Embeddings of PROOF.md Lemma 1 / Lemma 2 on small instances in the challenge's own semantics, the
edge count of `μ₃ × W₇`, and further definition edge cases and positive controls. -/

namespace WordRepTensor.ChallengeTests

/-! ### Lemma 2, n = 1, m = 2 : μ₅ ↪ μ₃ × W₅ and μ₅ ↪ μ'₃ × W₅ (fold 0,1,2,1,2) -/

def phi52 : Fin 5 → Fin 3 := ![0, 1, 2, 1, 2]

def iota52 : Fin 5 ⊕ Fin 5 ⊕ Unit → (Fin 3 ⊕ Fin 3 ⊕ Unit) × (Fin 5 ⊕ Unit)
  | .inl i => (.inl (phi52 i), .inl i)
  | .inr (.inl i) => (.inr (.inl (phi52 i)), .inl i)
  | .inr (.inr u) => (.inr (.inr u), .inr ())

example : Function.Injective iota52 := by decide
example : ∀ x y, (mu 5).Adj x y ↔ (tensorProd (mu 3) (wheel 5)).Adj (iota52 x) (iota52 y) := by
  decide +kernel
example : ∀ x y, (mu 5).Adj x y ↔ (tensorProd (muExt 3) (wheel 5)).Adj (iota52 x) (iota52 y) := by
  decide +kernel

/-! ### Lemma 2, n = 1, m = 3 : μ₇ ↪ μ₃ × W₇ (the controller's target graph) -/

def phi73 : Fin 7 → Fin 3 := ![0, 1, 2, 1, 2, 1, 2]

def iota73 : Fin 7 ⊕ Fin 7 ⊕ Unit → (Fin 3 ⊕ Fin 3 ⊕ Unit) × (Fin 7 ⊕ Unit)
  | .inl i => (.inl (phi73 i), .inl i)
  | .inr (.inl i) => (.inr (.inl (phi73 i)), .inl i)
  | .inr (.inr u) => (.inr (.inr u), .inr ())

example : Function.Injective iota73 := by decide
example : ∀ x y, (mu 7).Adj x y ↔ (tensorProd (mu 3) (wheel 7)).Adj (iota73 x) (iota73 y) := by
  decide +kernel

/-! ### Lemma 1, n = 3, m = 2 : graph of a homomorphism μ₇ → W₅ and μ'₇ → W₅ (fold 0..4,3,4) -/

def psi75 : Fin 7 → Fin 5 := ![0, 1, 2, 3, 4, 3, 4]

def gr75 : Fin 7 ⊕ Fin 7 ⊕ Unit → (Fin 7 ⊕ Fin 7 ⊕ Unit) × (Fin 5 ⊕ Unit)
  | .inl i => (.inl i, .inl (psi75 i))
  | .inr (.inl i) => (.inr (.inl i), .inl (psi75 i))
  | .inr (.inr u) => (.inr (.inr u), .inr ())

def gr75' : Fin 7 ⊕ Fin 7 ⊕ Unit → (Fin 7 ⊕ Fin 7 ⊕ Unit) × (Fin 5 ⊕ Unit)
  | .inl i => (.inl i, .inl (psi75 i))
  | .inr (.inl i) => (.inr (.inl i), .inr ())
  | .inr (.inr u) => (.inr (.inr u), .inl 0)

example : ∀ x y, (mu 7).Adj x y ↔ (tensorProd (mu 7) (wheel 5)).Adj (gr75 x) (gr75 y) := by
  decide +kernel
example : ∀ x y, (muExt 7).Adj x y ↔ (tensorProd (muExt 7) (wheel 5)).Adj (gr75' x) (gr75' y) := by
  decide +kernel

/-! ### Sizes and edge cases -/

-- μ₃ × W₇ has 336 edges (672 ordered adjacent pairs), as in the Python constructors
example : (Finset.univ.filter (fun p : ((Fin 3 ⊕ Fin 3 ⊕ Unit) × (Fin 7 ⊕ Unit)) ×
    ((Fin 3 ⊕ Fin 3 ⊕ Unit) × (Fin 7 ⊕ Unit)) =>
    (tensorProd (mu 3) (wheel 7)).Adj p.1 p.2)).card = 672 := by decide +kernel

-- μ'₇ has 7 + 7·6 + 7 = 56 edges; W₅ has 10 edges
example : (Finset.univ.filter (fun p : (Fin 7 ⊕ Fin 7 ⊕ Unit) × (Fin 7 ⊕ Fin 7 ⊕ Unit) =>
    (muExt 7).Adj p.1 p.2)).card = 112 := by decide +kernel
example : (Finset.univ.filter (fun p : (Fin 5 ⊕ Unit) × (Fin 5 ⊕ Unit) =>
    (wheel 5).Adj p.1 p.2)).card = 20 := by decide

-- no loops anywhere
example : ∀ x, ¬ (tensorProd (mu 3) (wheel 5)).Adj x x := by decide +kernel

-- a letter that does not occur: Alternate is then decided by the other letter's count only
example : Alternate [1] (0 : ℕ) 1 := by decide
example : ¬ Alternate [1, 1] (0 : ℕ) 1 := by decide
-- a word missing a vertex never represents
example : ¬ Represents (⊤ : SimpleGraph (Fin 3)) [0, 1] := by decide
-- C₅ (0-1-2-3-4-0) is represented by a 2-uniform word (positive control for a non-complete,
-- non-bipartite graph)
example : Represents (cycleGraph 5) [0, 4, 1, 0, 2, 1, 3, 2, 4, 3] := by decide

-- positive control on a product vertex type: K₂ × K₂ = 2K₂ is represented by abab cdcd
example : Represents (tensorProd (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)))
    [(0, 0), (1, 1), (0, 0), (1, 1), (0, 1), (1, 0), (0, 1), (1, 0)] := by decide
-- and a wrong word for it is rejected
example : ¬ Represents (tensorProd (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)))
    [(0, 0), (0, 1), (1, 1), (1, 0)] := by decide

/-! ### Non-vacuity of the §4 lemma statements (REVIEW-CHALLENGE.md §2,
`review/ReviewerProposedDefs.lean`): a homomorphism `μ₅ → W₅` (Lemma 1 shape, n = m = 2) -/

example : Nonempty (mu 5 →g wheel 5) :=
  ⟨{ toFun := fun x => match x with
        | .inl i => .inl i
        | .inr (.inl i) => .inl i
        | .inr (.inr _) => .inr ()
     map_rel' := by decide }⟩

/-! ### False controls (REVIEW-CHALLENGE.md §4, `review/ReviewerNegControl.lean` and
`review/ReviewerNegControl2.lean`).  The reviewer's five deliberately false claims, stated here
negated, so each line checks that the corresponding wrong claim is refuted. -/

-- 0 and 2 are not adjacent in C₅ (same as the check in the cycle section above)
example : ¬ (cycleGraph 5).Adj 0 2 := by decide
-- the word 0123 does not represent C₄ (same as the check in the representation section above)
example : ¬ Represents (cycleGraph 4) [0, 1, 2, 3] := by decide
-- the degree of (root, hub) in μ₃ × W₇ is not 20 (it is 21)
example : (Finset.univ.filter (fun q : (Fin 3 ⊕ Fin 3 ⊕ Unit) × (Fin 7 ⊕ Unit) =>
    (tensorProd (mu 3) (wheel 7)).Adj (.inr (.inr ()), .inr ()) q)).card ≠ 20 := by decide

-- a wrong map (root sent to (root, rim 0) instead of (root, hub)) is not an induced embedding
def bad52 : Fin 5 ⊕ Fin 5 ⊕ Unit → (Fin 3 ⊕ Fin 3 ⊕ Unit) × (Fin 5 ⊕ Unit)
  | .inl i => (.inl (phi52 i), .inl i)
  | .inr (.inl i) => (.inr (.inl (phi52 i)), .inl i)
  | .inr (.inr u) => (.inr (.inr u), .inl 0)

example : ¬ (∀ x y, (mu 5).Adj x y ↔ (tensorProd (mu 3) (wheel 5)).Adj (bad52 x) (bad52 y)) := by
  decide +kernel
-- the number of ordered adjacent pairs of μ₃ × W₇ is not 670 (it is 672)
example : (Finset.univ.filter (fun p : ((Fin 3 ⊕ Fin 3 ⊕ Unit) × (Fin 7 ⊕ Unit)) ×
    ((Fin 3 ⊕ Fin 3 ⊕ Unit) × (Fin 7 ⊕ Unit)) =>
    (tensorProd (mu 3) (wheel 7)).Adj p.1 p.2)).card ≠ 670 := by decide +kernel

end WordRepTensor.ChallengeTests
