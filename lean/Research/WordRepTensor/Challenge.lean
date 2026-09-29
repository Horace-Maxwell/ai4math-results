import Mathlib

/-!
# Challenge statements: word-representability of `μ_{2n+1} × W_{2m+1}` and `μ'_{2n+1} × W_{2m+1}`

Round-7 task `wordrep` (work folder `work/round7/wordrep/`).  This file contains ONLY definitions
and statements (`def … : Prop`); nothing is proved here.  After independent review the file is
frozen by SHA-256; phase C proves every `def … : Prop` below and a `Check.lean` states
`theorem check_X : Challenge.X := …` for each of them.

## Sources (exact wording and line numbers in `work/round7/wordrep/CONTRACT.md`)

* [A]  N. S. Alshammari, *On the Word-Representability of Tensor Product Graphs*,
  arXiv:2609.20881v1 (2026-09-16).  §1: alternation and word-representability; §1.1: wheel
  `W_n`, Mycielskian of the cycle `μ_n = μ(C_n)`, extended Mycielskian `μ'_n = μ'(C_n)`;
  §2, Definition 2.1: tensor product; §5 (Conclusion), Problem 5.1 (LaTeX label `prob1`):
  "Is it true that `μ_{2n+1} × W_{2m+1}` and `μ'_{2n+1} × W_{2m+1}` is always
  non-word-representable for `n ≥ 1` and `m ≥ 2`?"
* [KP] S. Kitaev, A. Pyatkin, *A note on semi-transitivity of Mycielski graphs*,
  arXiv:2408.05066v1 (journal version: "A note on Hameed's conjecture on the semi-transitivity of
  Mycielski graphs", Discuss. Math. Graph Theory 45 (2025)).  Theorem 4 (numbering of arXiv v1):
  `μ(C_{2k+1})` is not semi-transitive for all `k ≥ 1`; Remark 5: the same holds for
  `μ'(C_{2k+1})`.
  (Semi-transitive = word-representable by Halldórsson–Kitaev–Pyatkin 2016.)  These are the
  cited facts our proof of Problem 5.1 uses; they are stated here as `MycielskiOddCycleNotWR` and
  `ExtMycielskiOddCycleNotWR` so that phase C formalizes them too (rule 3.5.2 (1)).

## Modelling conventions

* A word over `V` is a `List V`.  `Alternate w x y` holds iff, after deleting from `w` every
  letter other than `x` and `y`, no two consecutive letters are equal, i.e. the remaining word is
  `xyxy⋯` or `yxyx⋯` (any length) — [A, §1].
* `Represents G w`: every vertex occurs in `w`, and for distinct `x, y`:
  `G.Adj x y ↔ Alternate w x y`.  `WordRepresentable G := ∃ w, Represents G w` — [A, §1].
  (For an infinite vertex type no word contains every vertex, so only finite graphs can be
  word-representable; all graphs below are finite.)
* `cycleGraph n` is Mathlib's cycle on `Fin n` (`i ~ j ↔ i - j = 1 ∨ j - i = 1` in `Fin n`);
  for `n ≥ 3` this is the cycle `C_n`.
* `wheel n` lives on `Fin n ⊕ Unit`: the rim `inl i` carries `cycleGraph n`, and the hub
  `inr ()` is adjacent to every rim vertex — [A, §1.1, "Wheel graph"].
* `mycielskian G` lives on `V ⊕ V ⊕ Unit`: `inl a` is the original vertex `a` (top row),
  `inr (inl a)` its shadow, `inr (inr ())` the root.  Adjacency: `inl a ~ inl b ↔ a ~ b`;
  `inl a ~ inr (inl b) ↔ a ~ b` (a shadow is joined to the `G`-neighbours of its original);
  every shadow `~` root; nothing else (shadows pairwise non-adjacent, root not adjacent to the top
  row) — [A, §1.1], [KP, §1.1].  `extMycielskian G` is the same except
  `inl a ~ inr (inl b) ↔ a ≠ b` — [A, §1.1, "Extended Mycielski"], [KP, §1.1].
  Both graphs are built with `SimpleGraph.fromRel` (symmetrise, drop loops) from a Boolean
  relation that lists each unordered edge type once.
* `tensorProd G H` on `α × β`: `(a, b) ~ (a', b') ↔ a ~ a' ∧ b ~ b'` — [A, Def. 2.1].
-/

set_option autoImplicit false

namespace WordRepTensor.Challenge

open SimpleGraph

/-! ## 1. Words and word-representability -/

/-- `noRepeat u = true` iff no two consecutive entries of `u` are equal. -/
def noRepeat {V : Type*} [DecidableEq V] : List V → Bool
  | a :: b :: t => (a != b) && noRepeat (b :: t)
  | _ => true

/-- `x` and `y` alternate in `w`: deleting all other letters leaves `xyxy⋯` or `yxyx⋯`. -/
def Alternate {V : Type*} [DecidableEq V] (w : List V) (x y : V) : Prop :=
  noRepeat (w.filter (fun z => z == x || z == y)) = true

/-- The word `w` represents the graph `G`. -/
def Represents {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : List V) : Prop :=
  (∀ v : V, v ∈ w) ∧ ∀ x y : V, x ≠ y → (G.Adj x y ↔ Alternate w x y)

/-- `G` is word-representable. -/
def WordRepresentable {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ w : List V, Represents G w

instance {V : Type*} [DecidableEq V] (w : List V) (x y : V) : Decidable (Alternate w x y) :=
  inferInstanceAs (Decidable (noRepeat (w.filter (fun z => z == x || z == y)) = true))

instance {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : List V) : Decidable (Represents G w) :=
  inferInstanceAs (Decidable ((∀ v : V, v ∈ w) ∧ ∀ x y : V, x ≠ y → (G.Adj x y ↔ Alternate w x y)))

/-! ## 2. Graphs -/

/-- Tensor (direct, Kronecker) product: `(a, b) ~ (a', b') ↔ a ~ a' ∧ b ~ b'`. -/
def tensorProd {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) :=
  SimpleGraph.fromRel fun p q => G.Adj p.1 q.1 ∧ H.Adj p.2 q.2

instance {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) [DecidableEq α] [DecidableEq β]
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (tensorProd G H).Adj :=
  fun p q => inferInstanceAs (Decidable (p ≠ q ∧ ((G.Adj p.1 q.1 ∧ H.Adj p.2 q.2) ∨
    (G.Adj q.1 p.1 ∧ H.Adj q.2 p.2))))

/-- Edge types of the wheel: rim–rim along the cycle, hub–rim. -/
def wheelRel (n : ℕ) : Fin n ⊕ Unit → Fin n ⊕ Unit → Bool
  | .inl i, .inl j => decide ((cycleGraph n).Adj i j)
  | .inr _, .inl _ => true
  | _, _ => false

/-- The wheel `W_n`: the cycle `C_n` on `inl 0, …, inl (n-1)` plus the hub `inr ()`. -/
def wheel (n : ℕ) : SimpleGraph (Fin n ⊕ Unit) :=
  SimpleGraph.fromRel fun a b => wheelRel n a b = true

instance (n : ℕ) : DecidableRel (wheel n).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ (wheelRel n a b = true ∨ wheelRel n b a = true)))

/-- Edge types of the Mycielskian: top–top (`a ~ b`), top `a`–shadow `b` (`a ~ b`),
shadow–root. -/
def mycRel {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] :
    V ⊕ V ⊕ Unit → V ⊕ V ⊕ Unit → Bool
  | .inl a, .inl b => decide (G.Adj a b)
  | .inl a, .inr (.inl b) => decide (G.Adj a b)
  | .inr (.inl _), .inr (.inr _) => true
  | _, _ => false

/-- The Mycielskian `μ(G)` (top row `inl`, shadows `inr ∘ inl`, root `inr (inr ())`). -/
def mycielskian {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph (V ⊕ V ⊕ Unit) :=
  SimpleGraph.fromRel fun a b => mycRel G a b = true

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (mycielskian G).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ (mycRel G a b = true ∨ mycRel G b a = true)))

/-- Edge types of the extended Mycielskian: as `mycRel`, but top `a`–shadow `b` iff `a ≠ b`. -/
def extMycRel {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    V ⊕ V ⊕ Unit → V ⊕ V ⊕ Unit → Bool
  | .inl a, .inl b => decide (G.Adj a b)
  | .inl a, .inr (.inl b) => decide (a ≠ b)
  | .inr (.inl _), .inr (.inr _) => true
  | _, _ => false

/-- The extended Mycielskian `μ'(G)`. -/
def extMycielskian {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph (V ⊕ V ⊕ Unit) :=
  SimpleGraph.fromRel fun a b => extMycRel G a b = true

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (extMycielskian G).Adj :=
  fun a b => inferInstanceAs
    (Decidable (a ≠ b ∧ (extMycRel G a b = true ∨ extMycRel G b a = true)))

/-- `μ_n = μ(C_n)` in the notation of [A]. -/
abbrev mu (n : ℕ) : SimpleGraph (Fin n ⊕ Fin n ⊕ Unit) := mycielskian (cycleGraph n)

/-- `μ'_n = μ'(C_n)` in the notation of [A]. -/
abbrev muExt (n : ℕ) : SimpleGraph (Fin n ⊕ Fin n ⊕ Unit) := extMycielskian (cycleGraph n)

/-! ## 3. Statements -/

/-- **Problem 5.1 of [A] (label `prob1`), `μ` part (answer: yes).**  For all `n ≥ 1` and
`m ≥ 2`, the tensor product `μ_{2n+1} × W_{2m+1}` is not word-representable. -/
def Problem1Mu : Prop :=
  ∀ n m : ℕ, 1 ≤ n → 2 ≤ m → ¬ WordRepresentable (tensorProd (mu (2 * n + 1)) (wheel (2 * m + 1)))

/-- **Problem 5.1 of [A] (label `prob1`), `μ'` part (answer: yes).**  For all `n ≥ 1` and
`m ≥ 2`, the tensor product `μ'_{2n+1} × W_{2m+1}` is not word-representable. -/
def Problem1MuExt : Prop :=
  ∀ n m : ℕ, 1 ≤ n → 2 ≤ m →
    ¬ WordRepresentable (tensorProd (muExt (2 * n + 1)) (wheel (2 * m + 1)))

/-- **[KP, Theorem 4]** (arXiv:2408.05066v1 numbering; word-representability form via HKP)
(cited ingredient): `μ(C_{2k+1})` is not word-representable, `k ≥ 1`. -/
def MycielskiOddCycleNotWR : Prop :=
  ∀ k : ℕ, 1 ≤ k → ¬ WordRepresentable (mu (2 * k + 1))

/-- **[KP, Remark 5]** (cited ingredient; also Hameed, DAM 359 (2024)):
`μ'(C_{2k+1})` is not word-representable, `k ≥ 1`. -/
def ExtMycielskiOddCycleNotWR : Prop :=
  ∀ k : ℕ, 1 ≤ k → ¬ WordRepresentable (muExt (2 * k + 1))

/-! ## 4. Lemmas used by the proof of Problem 5.1 (PROOF.md §4) -/

/-- Heredity [Kitaev–Lozin, *Words and Graphs*]: a graph isomorphic to an induced subgraph of a
word-representable graph is word-representable (`G ↪g H`: injective, adjacency preserved and
reflected). -/
def WordRepresentableOfEmbedding : Prop :=
  ∀ (V W : Type) [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W),
    Nonempty (G ↪g H) → WordRepresentable H → WordRepresentable G

/-- Graph of a homomorphism: if `G →g H` then `x ↦ (x, h x)` embeds `G` as an induced subgraph
of `G × H`. -/
def EmbeddingOfHom : Prop :=
  ∀ (V W : Type) (G : SimpleGraph V) (H : SimpleGraph W),
    Nonempty (G →g H) → Nonempty (G ↪g tensorProd G H)

/-- PROOF.md Lemma 1 (case `n ≥ m`), `μ` part: a homomorphism `μ_{2n+1} → W_{2m+1}`. -/
def Lemma1Mu : Prop :=
  ∀ n m : ℕ, 2 ≤ m → m ≤ n → Nonempty (mu (2 * n + 1) →g wheel (2 * m + 1))

/-- PROOF.md Lemma 1 (case `n ≥ m`), `μ'` part: a homomorphism `μ'_{2n+1} → W_{2m+1}`. -/
def Lemma1MuExt : Prop :=
  ∀ n m : ℕ, 2 ≤ m → m ≤ n → Nonempty (muExt (2 * n + 1) →g wheel (2 * m + 1))

/-- PROOF.md Lemma 2 (case `n ≤ m`): `μ_{2m+1}` is an induced subgraph of `μ_{2n+1} × W_{2m+1}`. -/
def Lemma2Mu : Prop :=
  ∀ n m : ℕ, 1 ≤ n → n ≤ m → 2 ≤ m →
    Nonempty (mu (2 * m + 1) ↪g tensorProd (mu (2 * n + 1)) (wheel (2 * m + 1)))

/-- PROOF.md Lemma 2 (case `n ≤ m`): `μ_{2m+1}` is an induced subgraph of `μ'_{2n+1} × W_{2m+1}`. -/
def Lemma2MuExt : Prop :=
  ∀ n m : ℕ, 1 ≤ n → n ≤ m → 2 ≤ m →
    Nonempty (mu (2 * m + 1) ↪g tensorProd (muExt (2 * n + 1)) (wheel (2 * m + 1)))

/-- (Optional) [A] Problem 5.1 as one proposition (answer: yes). -/
def Problem5_1 : Prop := Problem1Mu ∧ Problem1MuExt

end WordRepTensor.Challenge
