import Mathlib

set_option autoImplicit false

/-!
# Paper 5 back-fill: challenge statements (definitions and `Prop`s only, no proofs)

Paper: H. Dong, *Complete mappings of the Brauer and partial Brauer monoids*
(`papers/brauer-complete-mappings/note.tex`, release v1.4.0 and later).

Every numbered result of the paper (Theorem 1.1, Proposition 3.1, Lemmas 4.1–4.4, Remark 4.5,
Lemmas 5.1–5.4, Lemma 6.1, Proposition 6.2) has a `def … : Prop` below, together with the
load-bearing unnumbered claims of Sections 2, 3 and 5 (the classification of complete mappings of
`S_r`, the counting formulas, the ranks that occur, `J`-classes = rank classes, the group of units,
the idempotents `e_λ`, the fibres).

Conventions (see `STATEMENTS.md` for the full list of modelling choices):
* Points `[n]` are `Fin n` with paper point `k` = `Fin` index `k - 1`.
* A diagram of `PB_n` (blocks of size 1 or 2 of `[n] ∪ [n]'`) is encoded by the involution `x` of
  `Pt n = Fin n ⊕ Fin n` whose blocks are `{p, x p}` (`inl i` = top point, `inr i` = bottom point).
  `B_n` = the fixed-point-free ones.
* Products of diagrams: `dmul x y` draws `x` above `y` and keeps the connectivity of the outer
  points (`SimpleGraph.Reachable` in `SimpleGraph.fromRel` of the edges of the stacked picture).
* `S_r` is the paper's symmetric group with maps acting on the right (`gh` = first `g`, then `h`):
  `Sym r := (Equiv.Perm (Fin r))ᵐᵒᵖ`.
* Maps are written on the left (`α x` for the paper's `xα`).
-/

namespace BackfillPaper5.Challenge

open Function

/-! ## 1. Complete mappings -/

/-- A complete mapping of a magma `(S, op)`: a bijection `α` such that `x ↦ op x (α x)` is also a
bijection (paper, §1). -/
def IsCompleteMapping {S : Type*} (op : S → S → S) (α : S → S) : Prop :=
  Bijective α ∧ Bijective (fun x => op x (α x))

/-- The magma `(S, *)` has a complete mapping. -/
def HasCM (S : Type*) [Mul S] : Prop :=
  ∃ α : S → S, IsCompleteMapping (· * ·) α

/-- A subset `M` of `(S, op)`, viewed as a submagma, has a complete mapping: a bijection
`α : M → M` such that `x ↦ op x (α x)` takes values in `M` and is a bijection of `M`. -/
def SubsetHasCM {S : Type*} (op : S → S → S) (M : Set S) : Prop :=
  ∃ α : M → M, Bijective α ∧
    ∃ h : ∀ x : M, op x (α x) ∈ M, Bijective (fun x : M => (⟨op x (α x), h x⟩ : M))

/-- Two magmas are isomorphic. -/
def MagmaIso {A B : Type*} (opA : A → A → A) (opB : B → B → B) : Prop :=
  ∃ e : A ≃ B, ∀ x y, e (opA x y) = opB (e x) (e y)

/-! ## 2. The symmetric group and the sign -/

/-- The paper's `S_r`: permutations of `{1, …, r}` (here `Fin r`) acting on the right, so that
`g * h` means "first `g`, then `h`". For `g : Sym r` the image of `k` is `(MulOpposite.unop g) k`. -/
abbrev Sym (r : ℕ) := (Equiv.Perm (Fin r))ᵐᵒᵖ

/-- The sign `s : S_r → ℤ/2`, written additively: `0` exactly for even permutations. -/
def sgn {r : ℕ} (g : Sym r) : ZMod 2 :=
  if Equiv.Perm.sign (MulOpposite.unop g) = 1 then 0 else 1

/-- The transposition `(1 2)` of `S_r` (for `r ≥ 2`; `1` otherwise). -/
def swap12 (r : ℕ) : Sym r :=
  if h : 2 ≤ r then MulOpposite.op (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) else 1

/-! ## 3. Rees 0-matrix semigroups -/

/-- `M⁰(G, I, Λ, P)`: `none` is the zero and `some (i, g, λ)` is the triple `(i, g, λ)`.
The sandwich matrix is `P : Λ → I → Option G`, `P λ i = none` meaning `p_{λ i} = 0`. -/
abbrev Rees0 (G I Λ : Type*) := Option (I × G × Λ)

/-- The product of `M⁰(G, I, Λ, P)`:
`(i,a,λ)(j,b,μ) = (i, a p_{λ j} b, μ)` if `p_{λ j} ≠ 0`, and `0` otherwise; `0` is absorbing. -/
def rees0Mul {G I Λ : Type*} [Mul G] (P : Λ → I → Option G) :
    Rees0 G I Λ → Rees0 G I Λ → Rees0 G I Λ
  | none, _ => none
  | some _, none => none
  | some (i, a, l), some (j, b, m) => (P l j).map (fun p => (i, a * p * b, m))

/-- `𝓜₂ = M⁰(ℤ/2, H, H, Q)` with `ℤ/2` written additively (paper, §4). -/
def mulZ2 {H : Type*} (Q : H → H → Option (ZMod 2)) :
    Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H)
  | none, _ => none
  | some _, none => none
  | some (i, a, l), some (j, b, m) => (Q l j).map (fun p => (i, a + p + b, m))

/-- The entrywise sign image `s(P)` of a matrix over `S_r ∪ {0}` (zero entries stay zero). -/
def sgnMat {r : ℕ} {H : Type*} (P : H → H → Option (Sym r)) : H → H → Option (ZMod 2) :=
  fun l j => (P l j).map sgn

/-- `s(p_{λ j})` (used only where `p_{λ j} ≠ 0`; the value `0` for a zero entry is a dummy). -/
def sOf {r : ℕ} {H : Type*} (P : H → H → Option (Sym r)) (l j : H) : ZMod 2 :=
  ((P l j).map sgn).getD 0

/-- A Latin square on `H`: `L i ·` and `L · λ` are bijections. -/
def IsLatin {H : Type*} (L : H → H → H) : Prop :=
  (∀ i, Bijective (L i)) ∧ (∀ l, Bijective (fun i => L i l))

/-- The map of Lemma 4.1: `0 ↦ 0`, `(i, g, λ) ↦ (λ, g phi, L(i, λ))`. -/
def fA {r : ℕ} {H : Type*} (L : H → H → H) (phi : Sym r → Sym r) :
    Rees0 (Sym r) H H → Rees0 (Sym r) H H
  | none => none
  | some (i, g, l) => some (l, phi g, L i l)

/-- The map `f̄` of Lemma 4.3 (`μ = L(i, λ)`): `(i, 1 + t μ, λ) ↦ (λ, 1, μ)`,
`(i, t μ, λ) ↦ (λ, 0, δ μ)`, `0 ↦ 0`. -/
def fB {H : Type*} (L : H → H → H) (δ : H → H) (t : H → ZMod 2) :
    Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H)
  | none => none
  | some (i, a, l) => if a = 1 + t (L i l) then some (l, 1, L i l) else some (l, 0, δ (L i l))

/-- The map `f̄` of Lemma 4.4: `(i, c λ, λ) ↦ (λ, 1 + c λ, L(i, λ))`,
`(i, 1 + c λ, λ) ↦ (ρ λ, c (ρ λ), L(i, ρ λ))`, `0 ↦ 0`. -/
def fC {H : Type*} (L : H → H → H) (ρ : H → H) (c : H → ZMod 2) :
    Option (H × ZMod 2 × H) → Option (H × ZMod 2 × H)
  | none => none
  | some (i, a, l) =>
      if a = c l then some (l, 1 + c l, L i l) else some (ρ l, c (ρ l), L i (ρ l))

/-- Condition `(∗)` of Lemma 4.4 for the cycle `(λ₀, …, λ_{m-1})` of `ρ` through `λ = λ₀`
(`λ_t = ρ^t λ`, `m` = length of the cycle = minimal period):
`m + Σ_{t<m} s(p_{λ_t λ_{t+1}}) ≡ 0 (mod 2)`. -/
def CycleCond {r : ℕ} {H : Type*} (P : H → H → Option (Sym r)) (ρ : Equiv.Perm H) (l : H) :
    Prop :=
  ((minimalPeriod ρ l : ℕ) : ZMod 2) +
    ∑ t ∈ Finset.range (minimalPeriod ρ l), sOf P ((ρ ^ t) l) ((ρ ^ (t + 1)) l) = 0

/-- The Brandt semigroup `B(S₂, 3) = M⁰(S₂, [3], [3], Δ₃)`: sandwich matrix `Δ₃` (identity). -/
def delta3 : Fin 3 → Fin 3 → Option (Sym 2) := fun l j => if l = j then some 1 else none

/-! ## 4. Diagrams, the product, rank -/

/-- The `2n` points `[n] ∪ [n]'`: `Sum.inl i` is the top point, `Sum.inr i` the bottom point. -/
abbrev Pt (n : ℕ) := Fin n ⊕ Fin n

/-- `x` encodes a partition of `[n] ∪ [n]'` into blocks `{p, x p}` of size 1 or 2
(Mathlib's `Function.Involutive`: `∀ p, x (x p) = p`). -/
def IsPB {n : ℕ} (x : Pt n → Pt n) : Prop := Function.Involutive x

/-- The partial Brauer monoid `PB_n` (as a set of encoded diagrams). -/
def PB (n : ℕ) : Set (Pt n → Pt n) := {x | IsPB x}

/-- The Brauer monoid `B_n`: all blocks have size 2. -/
def B (n : ℕ) : Set (Pt n → Pt n) := {x | Function.Involutive x ∧ ∀ p, x p ≠ p}

/-- The vertices of the stacked picture of `x` above `y` are `Fin 3 × Fin n`: row `0` is the top
row, row `1` the middle row, row `2` the bottom row. -/
abbrev SPt (n : ℕ) := Fin 3 × Fin n

/-- Points of `x`: its top row is row `0`, its bottom row is the middle row `1`. -/
def upper {n : ℕ} : Pt n → SPt n
  | .inl i => (0, i)
  | .inr i => (1, i)

/-- Points of `y`: its top row is the middle row `1`, its bottom row is row `2`. -/
def lower {n : ℕ} : Pt n → SPt n
  | .inl i => (1, i)
  | .inr i => (2, i)

/-- The outer points of the product: the top row of `x` (row `0`) and the bottom row of `y`
(row `2`). -/
def outer {n : ℕ} : Pt n → SPt n
  | .inl i => (0, i)
  | .inr i => (2, i)

/-- Edges of the stacked picture: each block `{p, x p}` of `x`, and each block `{p, y p}` of `y`. -/
def stackEdge {n : ℕ} (x y : Pt n → Pt n) (u v : SPt n) : Prop :=
  (∃ p, u = upper p ∧ v = upper (x p)) ∨ (∃ p, u = lower p ∧ v = lower (y p))

instance {n : ℕ} (x y : Pt n → Pt n) : DecidableRel (stackEdge x y) := fun u v =>
  inferInstanceAs
    (Decidable ((∃ p, u = upper p ∧ v = upper (x p)) ∨ (∃ p, u = lower p ∧ v = lower (y p))))

/-- The stacked picture as a Mathlib `SimpleGraph` (loops, i.e. singleton blocks, and edge
multiplicities play no role for connectivity). -/
abbrev stackGraph {n : ℕ} (x y : Pt n → Pt n) : SimpleGraph (SPt n) :=
  SimpleGraph.fromRel (stackEdge x y)

/-- The points of `[n] ∪ [n]'`, listed as `1, …, n, 1', …, n'`. -/
def ptList (n : ℕ) : List (Pt n) := (List.finRange n).map Sum.inl ++ (List.finRange n).map Sum.inr

/-- The product `xy` (paper, §2): draw `x` above `y`, identify the bottom row of `x` with the top
row of `y`, keep the connectivity of the outer points and discard everything else. The partner of
the outer point `p` is an outer point `q ≠ p` in the same connected component of the stacked
picture (Mathlib's `SimpleGraph.Reachable`), the first one in the list `ptList n` if there are
several (for diagrams of `PB_n` there is at most one); if there is none, `p` is a singleton.
Computable (Mathlib decides `Reachable` on finite graphs), so small cases can be checked. -/
def dmul {n : ℕ} (x y : Pt n → Pt n) (p : Pt n) : Pt n :=
  ((ptList n).find?
    (fun q => decide (q ≠ p ∧ (stackGraph x y).Reachable (outer p) (outer q)))).getD p

/-- The identity diagram (blocks `{i, i'}`). -/
def idD (n : ℕ) : Pt n → Pt n := Sum.swap

/-- The rank: the number of through blocks (blocks meeting both rows). -/
def rank {n : ℕ} (x : Pt n → Pt n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => (x (Sum.inl i)).isRight)).card

/-- The two families. -/
inductive Fam
  | B
  | PB
  deriving DecidableEq

/-- `D ∈ {B_n, PB_n}`. -/
def Dset : Fam → (n : ℕ) → Set (Pt n → Pt n)
  | .B, n => B n
  | .PB, n => PB n

/-- `J_r`: the elements of rank `r` of `D`. -/
def Jr (D : Fam) (n r : ℕ) : Set (Pt n → Pt n) := {x | x ∈ Dset D n ∧ rank x = r}

/-- The rank `r` occurs in `D`. -/
def RankOccurs (D : Fam) (n r : ℕ) : Prop := ∃ x ∈ Dset D n, rank x = r

/-! ## 5. Green's `J`-relation, principal factors -/

/-- Green's `J`-relation in a monoid `M ⊆ S` (for a monoid `S¹ = S`):
`x J y` iff `x = a y b` and `y = c x d` for some `a, b, c, d ∈ M`. -/
def JRel {S : Type*} (op : S → S → S) (M : Set S) (x y : S) : Prop :=
  ∃ a ∈ M, ∃ b ∈ M, ∃ c ∈ M, ∃ d ∈ M, x = op (op a y) b ∧ y = op (op c x) d

/-- The `J`-class of `x` in `M`. -/
def JClass {S : Type*} (op : S → S → S) (M : Set S) (x : S) : Set S :=
  {y | y ∈ M ∧ JRel op M x y}

/-- The principal factor `J⁰ = J ∪ {0}` (`none` is the new zero): the product of `x, y ∈ J` is
`xy` if `xy ∈ J` and `0` otherwise; `0` is absorbing. (The `DecidablePred` argument only decides
the `if`; any two instances give the same function, so the statements below use the classical
one, and the tests use computable ones.) -/
def pfMul {S : Type*} (op : S → S → S) (J : Set S) [DecidablePred (· ∈ J)] :
    Option J → Option J → Option J
  | some x, some y => if h : op x y ∈ J then some ⟨op x y, h⟩ else none
  | _, _ => none

/-- The principal factor `J⁰` has a complete mapping. -/
def PFHasCM {S : Type*} (op : S → S → S) (J : Set S) [DecidablePred (· ∈ J)] : Prop :=
  ∃ α : Option J → Option J, IsCompleteMapping (pfMul op J) α

/-! ## 6. Half-diagrams, Rees coordinates -/

/-- A half-diagram `(F, M)` on `[n]`, encoded as `(F, m)` where `m` is the involution of `[n]`
whose 2-cycles are the arcs of `M` (points on no arc are fixed). -/
abbrev Half (n : ℕ) := Finset (Fin n) × (Fin n → Fin n)

/-- `h = (F, m)` is a half-diagram of rank `r` for `D`: `|F| = r`, `m` is an involution fixing the
free points, and (for `B_n`) every point outside `F` lies on an arc. -/
def IsHalf (D : Fam) (n r : ℕ) (h : Half n) : Prop :=
  h.1.card = r ∧ (∀ a, h.2 (h.2 a) = a) ∧ (∀ a ∈ h.1, h.2 a = a) ∧
    (D = Fam.B → ∀ a, a ∉ h.1 → h.2 a ≠ a)

/-- `H_r(D)`. -/
def Hr (D : Fam) (n r : ℕ) : Set (Half n) := {h | IsHalf D n r h}

/-- `H_r(D)` as a type (index set of the Rees matrix semigroup). -/
abbrev HSub (D : Fam) (n r : ℕ) := {h : Half n // h ∈ Hr D n r}

/-- `top(x)`: free points = top points of through blocks; arcs = blocks inside the top row. -/
def topHalf {n : ℕ} (x : Pt n → Pt n) : Half n :=
  (Finset.univ.filter (fun i : Fin n => (x (Sum.inl i)).isRight),
    fun i => match x (Sum.inl i) with
      | Sum.inl j => j
      | Sum.inr _ => i)

/-- `bot(x)`: the same for the bottom row, primes removed. -/
def botHalf {n : ℕ} (x : Pt n → Pt n) : Half n :=
  (Finset.univ.filter (fun i : Fin n => (x (Sum.inr i)).isLeft),
    fun i => match x (Sum.inr i) with
      | Sum.inr j => j
      | Sum.inl _ => i)

/-- The 0-based position of `a` in `F` (number of smaller elements of `F`): the `k`-th smallest
point of `F` (paper, 1-based) has position `k - 1`. -/
def pos {n : ℕ} (F : Finset (Fin n)) (a : Fin n) : ℕ := (F.filter (· < a)).card

/-- `g` represents the through blocks of `x`: if `{a, b'}` is a block and `a` is the `k`-th
smallest top through point, then `b` is the `(k g)`-th smallest bottom through point. -/
def RepG {n : ℕ} (r : ℕ) (x : Pt n → Pt n) (g : Sym r) : Prop :=
  ∀ (k : Fin r) (a b : Fin n), x (Sum.inl a) = Sum.inr b → pos (topHalf x).1 a = k →
    ((MulOpposite.unop g) k : ℕ) = pos (botHalf x).1 b

open Classical in
/-- `g(x) ∈ S_r` (paper, §3). -/
noncomputable def gCoord {n : ℕ} (r : ℕ) (x : Pt n → Pt n) : Sym r :=
  if h : ∃ g, RepG r x g then h.choose else 1

/-- The edges of `Γ(λ, i)`: the arcs of `λ` and the arcs of `i`. -/
def GammaEdge {n : ℕ} (l i : Half n) (a b : Fin n) : Prop :=
  (l.2 a = b ∧ b ≠ a) ∨ (i.2 a = b ∧ b ≠ a)

instance {n : ℕ} (l i : Half n) : DecidableRel (GammaEdge l i) := fun a b =>
  inferInstanceAs (Decidable ((l.2 a = b ∧ b ≠ a) ∨ (i.2 a = b ∧ b ≠ a)))

/-- `Γ(λ, i)` as a Mathlib `SimpleGraph` on `[n]` (a double edge, i.e. an arc of both, is a
single edge; multiplicities play no role for connectivity). -/
abbrev gammaGraph {n : ℕ} (l i : Half n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (GammaEdge l i)

/-- `λ ∼ i`: the path of `Γ(λ, i)` starting at each point of `F(λ)` ends at a point of `F(i)`.
(All degrees are at most 2 and points of `F(λ)`, `F(i)` have degree at most 1, so the only point
of `F(i)` that can lie in the component of `a ∈ F(λ)` is the far end of the path from `a`; hence
this is: every `a ∈ F(λ)` is connected to some point of `F(i)`.) -/
def Compat {n : ℕ} (l i : Half n) : Prop :=
  ∀ a ∈ l.1, ∃ e ∈ i.1, (gammaGraph l i).Reachable a e

/-- `p` represents the matching of `F(λ)` with `F(i)` along the paths of `Γ(λ, i)`. -/
def RepP {n : ℕ} (r : ℕ) (l i : Half n) (p : Sym r) : Prop :=
  ∀ (k : Fin r) (a e : Fin n), a ∈ l.1 → e ∈ i.1 → pos l.1 a = k → (gammaGraph l i).Reachable a e →
    ((MulOpposite.unop p) k : ℕ) = pos i.1 e

open Classical in
/-- `p_{λ i} ∈ S_r` (meaningful when `λ ∼ i`). -/
noncomputable def pSand {n : ℕ} (r : ℕ) (l i : Half n) : Sym r :=
  if h : ∃ p, RepP r l i p then h.choose else 1

open Classical in
/-- The sandwich matrix `P`: `p_{λ i}` if `λ ∼ i`, and `0` otherwise. -/
noncomputable def sand {n : ℕ} (r : ℕ) (l i : Half n) : Option (Sym r) :=
  if Compat l i then some (pSand r l i) else none

/-- `P` restricted to the index set `H_r(D)`. -/
noncomputable def sandSub (D : Fam) (n r : ℕ) : HSub D n r → HSub D n r → Option (Sym r) :=
  fun l i => sand r l.1 i.1

/-- The idempotent `e_λ`: top and bottom halves `λ`, through blocks `{a, a'}` for `a ∈ F(λ)`. -/
def eDiag {n : ℕ} (l : Half n) : Pt n → Pt n
  | Sum.inl a => if a ∈ l.1 then Sum.inr a else Sum.inl (l.2 a)
  | Sum.inr a => if a ∈ l.1 then Sum.inl a else Sum.inr (l.2 a)

/-! ## 7. The half-diagrams of §5 -/

/-- The perfect matching `R₀ = {r+3, r+4}, {r+5, r+6}, …` of `{r+3, …, n}` (paper points;
here 0-based: `r+2 ↔ r+3`, `r+4 ↔ r+5`, …); other points are fixed. -/
def r0 (n r : ℕ) (a : Fin n) : Fin n :=
  if r + 2 ≤ a.val then
    (if (a.val - (r + 2)) % 2 = 0 then
      (if h : a.val + 1 < n then ⟨a.val + 1, h⟩ else a)
    else ⟨a.val - 1, by have := a.isLt; omega⟩)
  else a

/-- The partner `c_j` of the point `1` in `I_j` (paper points `2, 3, 4`; here 0-based `1, 2, 3`). -/
def triPartner : Fin 3 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3

/-- The half-diagrams `I_0, I_1, I_2` of Lemma 5.2, 0-based:
`I_j = (F_j, {{0, c_j}} ∪ R₀)` with `F_j = {a < r + 2 : a ≠ 0, a ≠ c_j}`; so
`F_0 = {2,3} ∪ E`, `F_1 = {1,3} ∪ E`, `F_2 = {1,2} ∪ E` with `E = ∅` (`r = 2`) or `{4}` (`r = 3`),
i.e. paper points `{3,4} ∪ E`, `{2,4} ∪ E`, `{2,3} ∪ E` with `E = ∅` or `{5}`. -/
def triHalf (n r : ℕ) (j : Fin 3) : Half n :=
  (Finset.univ.filter (fun a : Fin n => a.val < r + 2 ∧ a.val ≠ 0 ∧ a.val ≠ triPartner j),
    fun a =>
      if a.val = 0 then (if h : triPartner j < n then ⟨triPartner j, h⟩ else a)
      else if a.val = triPartner j then (if h : 0 < n then ⟨0, h⟩ else a)
      else r0 n r a)

/-- The number `a(k)` of involutions of a `k`-set. -/
noncomputable def invCount (k : ℕ) : ℕ := Nat.card {σ : Equiv.Perm (Fin k) // σ * σ = 1}

/-! ## 8. Statements -/

open scoped Nat

/-- Model sanity (not a claim of the paper): `PB_n` and `B_n` are closed under the product, and
the identity diagram is a two-sided identity. -/
def ModelMonoid : Prop :=
  ∀ n : ℕ, (∀ x ∈ PB n, ∀ y ∈ PB n, dmul x y ∈ PB n) ∧ (∀ x ∈ B n, ∀ y ∈ B n, dmul x y ∈ B n) ∧
    idD n ∈ B n ∧ ∀ x ∈ PB n, dmul (idD n) x = x ∧ dmul x (idD n) = x

/-- §2: `rank(xy) ≤ min(rank x, rank y)`. -/
def RankMul : Prop :=
  ∀ n : ℕ, ∀ x ∈ PB n, ∀ y ∈ PB n, rank (dmul x y) ≤ min (rank x) (rank y)

/-- §2 (cited from [EMRT]): the `J`-classes of `B_n` and `PB_n` are the rank classes. -/
def JClassesAreRankClasses : Prop :=
  ∀ (D : Fam) (n : ℕ), ∀ x ∈ Dset D n, ∀ y ∈ Dset D n,
    (JRel dmul (Dset D n) x y ↔ rank x = rank y)

/-- §2: `J_r` of `B_n` is non-empty exactly when `r ≤ n` and `r ≡ n (mod 2)`; in `PB_n` exactly
when `r ≤ n`. -/
def RanksOccurring : Prop :=
  ∀ n r : ℕ, (RankOccurs Fam.B n r ↔ r ≤ n ∧ r % 2 = n % 2) ∧ (RankOccurs Fam.PB n r ↔ r ≤ n)

/-- §2: the group of units is `J_n`, the permutation diagrams, and it is isomorphic to `S_n`. -/
def UnitsAreSym : Prop :=
  ∀ (D : Fam) (n : ℕ),
    (∀ x ∈ Dset D n,
      (∃ y ∈ Dset D n, dmul x y = idD n ∧ dmul y x = idD n) ↔ rank x = n) ∧
    ∃ e : Sym n ≃ Jr D n n, ∀ g h : Sym n, ((e (g * h) : Jr D n n) : Pt n → Pt n) = dmul (e g) (e h)

/-- §2 (from (R1), Hall–Paige): `S_r` has a complete mapping iff `r ∉ {2, 3}`. -/
def SymCM : Prop := ∀ r : ℕ, HasCM (Sym r) ↔ (r ≠ 2 ∧ r ≠ 3)

/-- The same with Mathlib's composition convention for `Equiv.Perm` (convention independence). -/
def SymCMPerm : Prop := ∀ r : ℕ, HasCM (Equiv.Perm (Fin r)) ↔ (r ≠ 2 ∧ r ≠ 3)

/-- (R2) (cited): a complete mapping of a magma with zero fixes the zero. -/
def ZeroFixed : Prop :=
  ∀ (S : Type) (op : S → S → S) (z : S), (∀ x, op z x = z ∧ op x z = z) →
    ∀ α : S → S, IsCompleteMapping op α → α z = z

/-- §3: `N = C(n,r) (n-r-1)!!` for `B_n` and `N = C(n,r) a(n-r)` for `PB_n`. -/
def CountH : Prop :=
  (∀ n r : ℕ, r ≤ n → r % 2 = n % 2 → (Hr Fam.B n r).ncard = n.choose r * (n - r - 1)‼) ∧
    (∀ n r : ℕ, r ≤ n → (Hr Fam.PB n r).ncard = n.choose r * invCount (n - r))

/-- **Proposition 3.1 (a)**: `x ↦ (top x, g x, bot x)` is a bijection `J_r → H × S_r × H`. -/
def Prop31a : Prop :=
  ∀ (D : Fam) (n r : ℕ), RankOccurs D n r →
    Set.BijOn (fun x => (topHalf x, gCoord r x, botHalf x)) (Jr D n r)
      (Hr D n r ×ˢ (Set.univ ×ˢ Hr D n r))

/-- **Proposition 3.1 (b)**: for `x, y ∈ J_r`, `rank(xy) = r` iff `bot x ∼ top y`, and then
`top(xy) = top x`, `bot(xy) = bot y`, `g(xy) = g(x) p_{bot x, top y} g(y)`. -/
def Prop31b : Prop :=
  ∀ (D : Fam) (n r : ℕ), ∀ x ∈ Jr D n r, ∀ y ∈ Jr D n r,
    (rank (dmul x y) = r ↔ Compat (botHalf x) (topHalf y)) ∧
    (Compat (botHalf x) (topHalf y) →
      topHalf (dmul x y) = topHalf x ∧ botHalf (dmul x y) = botHalf y ∧
      gCoord r (dmul x y) = gCoord r x * pSand r (botHalf x) (topHalf y) * gCoord r y)

/-- **Proposition 3.1 (c)**: `λ ∼ λ`, `p_{λλ} = 1`; `λ ∼ i ↔ i ∼ λ`, and then
`p_{iλ} = p_{λi}⁻¹`. -/
def Prop31c : Prop :=
  ∀ (D : Fam) (n r : ℕ), ∀ l ∈ Hr D n r, ∀ i ∈ Hr D n r,
    Compat l l ∧ pSand r l l = 1 ∧ (Compat l i ↔ Compat i l) ∧
      (Compat l i → pSand r i l = (pSand r l i)⁻¹)

/-- **Proposition 3.1 (d)**: if `F(λ) = F(i)` then `λ ∼ i` and `p_{λi} = 1`. -/
def Prop31d : Prop :=
  ∀ (D : Fam) (n r : ℕ), ∀ l ∈ Hr D n r, ∀ i ∈ Hr D n r, l.1 = i.1 →
    Compat l i ∧ pSand r l i = 1

open Classical in
/-- **Proposition 3.1, consequence**: `J_r⁰ ≅ M⁰(S_r, H, H, P)` by an isomorphism extending the
map of (a) by `0 ↦ 0`. -/
def Prop31iso : Prop :=
  ∀ (D : Fam) (n r : ℕ), RankOccurs D n r →
    ∃ e : Option (Jr D n r) ≃ Option (HSub D n r × Sym r × HSub D n r),
      e none = none ∧
      (∀ (x : Jr D n r) (t : HSub D n r × Sym r × HSub D n r), e (some x) = some t →
        t.1.1 = topHalf x.1 ∧ t.2.1 = gCoord r x.1 ∧ t.2.2.1 = botHalf x.1) ∧
      ∀ u v, e (pfMul dmul (Jr D n r) u v) = rees0Mul (sandSub D n r) (e u) (e v)

/-- §3 (after Proposition 3.1): `e_λ` has coordinates `(λ, 1, λ)` and is an idempotent, and its
`𝓗`-class `{(λ, g, λ)}` is a group isomorphic to `S_r`: `(λ,g,λ)(λ,h,λ) = (λ, gh, λ)`. -/
def IdempotentE : Prop :=
  ∀ (D : Fam) (n r : ℕ), ∀ l ∈ Hr D n r,
    eDiag l ∈ Jr D n r ∧ topHalf (eDiag l) = l ∧ botHalf (eDiag l) = l ∧
    gCoord r (eDiag l) = 1 ∧ dmul (eDiag l) (eDiag l) = eDiag l ∧
    ∀ x ∈ Jr D n r, ∀ y ∈ Jr D n r, topHalf x = l → botHalf x = l → topHalf y = l →
      botHalf y = l →
      dmul x y ∈ Jr D n r ∧ topHalf (dmul x y) = l ∧ botHalf (dmul x y) = l ∧
        gCoord r (dmul x y) = gCoord r x * gCoord r y

/-- **Lemma 4.1**: if `S_r` has a complete mapping `phi`, then `f = fA L phi` is a complete mapping
of `M⁰(S_r, H, H, P)` (identity diagonal, `L` a Latin square). -/
def Lemma41 : Prop :=
  ∀ (r : ℕ) (H : Type) [Finite H] [Nonempty H] (P : H → H → Option (Sym r))
    (L : H → H → H) (phi : Sym r → Sym r),
    (∀ l, P l l = some 1) → IsLatin L → IsCompleteMapping (· * ·) phi →
      IsCompleteMapping (rees0Mul P) (fA L phi)

/-- **Lemma 4.2 (lifting)**: for `r ∈ {2,3}`, if `𝓜₂ = M⁰(ℤ/2, H, H, s(P))` has a complete mapping,
so does `M⁰(S_r, H, H, P)`. -/
def Lemma42 : Prop :=
  ∀ (r : ℕ), (r = 2 ∨ r = 3) → ∀ (H : Type) [Finite H] [Nonempty H]
    (P : H → H → Option (Sym r)), (∀ l, P l l = some 1) →
    (∃ f, IsCompleteMapping (mulZ2 (sgnMat P)) f) → ∃ f, IsCompleteMapping (rees0Mul P) f

/-- **Lemma 4.3**: (i) for `t (δ μ) = t μ + 1`, `fB L δ t` is a complete mapping of `𝓜₂`;
(ii) such `δ, t` exist when `N = |H|` is even, and then `M⁰(S_r, H, H, P)` has a complete
mapping. -/
def Lemma43 : Prop :=
  ∀ (r : ℕ), (r = 2 ∨ r = 3) → ∀ (H : Type) [Finite H] [Nonempty H]
    (P : H → H → Option (Sym r)), (∀ l, P l l = some 1) →
    (∀ (L : H → H → H) (δ : Equiv.Perm H) (t : H → ZMod 2), IsLatin L →
        (∀ μ, t (δ μ) = t μ + 1) → IsCompleteMapping (mulZ2 (sgnMat P)) (fB L δ t)) ∧
    (Even (Nat.card H) →
      (∃ (δ : Equiv.Perm H) (t : H → ZMod 2), ∀ μ, t (δ μ) = t μ + 1) ∧
        ∃ f, IsCompleteMapping (rees0Mul P) f)

/-- **Lemma 4.4**: for `ρ` with `λ ∼ λρ` and `(∗)` on every cycle: (i) there is `c` with
`c(λρ) = c(λ) + 1 + s(p_{λ,λρ})`; (ii) for such `c`, `fC L ρ c` is a complete mapping of `𝓜₂`;
(iii) hence `M⁰(S_r, H, H, P)` has a complete mapping. -/
def Lemma44 : Prop :=
  ∀ (r : ℕ), (r = 2 ∨ r = 3) → ∀ (H : Type) [Finite H] [Nonempty H]
    (P : H → H → Option (Sym r)), (∀ l, P l l = some 1) →
    ∀ ρ : Equiv.Perm H, (∀ l, P l (ρ l) ≠ none) → (∀ l, CycleCond P ρ l) →
      (∃ c : H → ZMod 2, ∀ l, c (ρ l) = c l + 1 + sOf P l (ρ l)) ∧
      (∀ (L : H → H → H) (c : H → ZMod 2), IsLatin L →
        (∀ l, c (ρ l) = c l + 1 + sOf P l (ρ l)) →
          IsCompleteMapping (mulZ2 (sgnMat P)) (fC L ρ c)) ∧
      ∃ f, IsCompleteMapping (rees0Mul P) f

/-- **Remark 4.5 (1)**: under the hypotheses of Lemma 4.4, `ρ` has no fixed points. -/
def Remark45a : Prop :=
  ∀ (r : ℕ) (H : Type) [Finite H] (P : H → H → Option (Sym r)) (ρ : Equiv.Perm H),
    (∀ l, P l l = some 1) → (∀ l, CycleCond P ρ l) → ∀ l, ρ l ≠ l

/-- **Remark 4.5 (2)**: if `λ ∼ μ` implies `μ ∼ λ` and `p_{μλ} = p_{λμ}⁻¹`, every 2-cycle
`(a b)` of `ρ` with `a ∼ b` satisfies `(∗)`. -/
def Remark45b : Prop :=
  ∀ (r : ℕ) (H : Type) [Finite H] (P : H → H → Option (Sym r)),
    (∀ l m p, P l m = some p → P m l = some p⁻¹) →
    ∀ (ρ : Equiv.Perm H) (l : H), ρ l ≠ l → ρ (ρ l) = l → P l (ρ l) ≠ none → CycleCond P ρ l

/-- **Remark 4.5 (3)**: a 3-cycle `(a b c)` of `ρ` satisfies `(∗)` iff
`s(p_ab) + s(p_bc) + s(p_ca) = 1`, i.e. iff `p_ab p_bc p_ca` is odd. -/
def Remark45c : Prop :=
  ∀ (r : ℕ) (H : Type) [Finite H] (P : H → H → Option (Sym r)) (ρ : Equiv.Perm H) (l : H)
    (pab pbc pca : Sym r),
    ρ l ≠ l → (ρ ^ 3) l = l →
    P l (ρ l) = some pab → P (ρ l) ((ρ ^ 2) l) = some pbc → P ((ρ ^ 2) l) l = some pca →
    (CycleCond P ρ l ↔ sgn pab + sgn pbc + sgn pca = 1) ∧
      (sgn pab + sgn pbc + sgn pca = 1 ↔ sgn (pab * pbc * pca) = 1)

/-- §5 (fibres): for `D = B_n`, `r ≤ n`, `r ≡ n (mod 2)` and `|F| = r`, the fibre `H_F` has
`m = (n-r-1)!!` elements, an odd number. -/
def FibreCount : Prop :=
  ∀ n r : ℕ, r ≤ n → r % 2 = n % 2 → ∀ F : Finset (Fin n), F.card = r →
    {h | h ∈ Hr Fam.B n r ∧ h.1 = F}.ncard = (n - r - 1)‼ ∧ Odd ((n - r - 1)‼)

/-- **Lemma 5.1**: (for `B_n`, `r ∈ {2,3}`, `r < n`, `n ≡ r`) `N` is odd iff `r = 2, n ≡ 2 (mod 4)`
or `r = 3, n ≡ 3 (mod 4)`; then `n - r ≥ 4` and `C(n,r)` is odd. -/
def Lemma51 : Prop :=
  ∀ n r : ℕ, (r = 2 ∨ r = 3) → r < n → n % 2 = r % 2 →
    (Odd (Hr Fam.B n r).ncard ↔ (r = 2 ∧ n % 4 = 2) ∨ (r = 3 ∧ n % 4 = 3)) ∧
    (Odd (Hr Fam.B n r).ncard → 4 ≤ n - r ∧ Odd (n.choose r))

/-- **Lemma 5.2 (the triangle)**: for `n - r ≥ 2`, `I_0 ∼ I_1 ∼ I_2 ∼ I_0` with
`p_{I₀I₁} = p_{I₁I₂} = 1`, `p_{I₂I₀} = (1 2)`; in particular the product is odd.
(Also: the `I_j` are half-diagrams of rank `r`.) -/
def Lemma52 : Prop :=
  ∀ n r : ℕ, (r = 2 ∨ r = 3) → r + 2 ≤ n → n % 2 = r % 2 →
    (∀ j, triHalf n r j ∈ Hr Fam.B n r) ∧
    Compat (triHalf n r 0) (triHalf n r 1) ∧ Compat (triHalf n r 1) (triHalf n r 2) ∧
    Compat (triHalf n r 2) (triHalf n r 0) ∧
    pSand r (triHalf n r 0) (triHalf n r 1) = 1 ∧ pSand r (triHalf n r 1) (triHalf n r 2) = 1 ∧
    pSand r (triHalf n r 2) (triHalf n r 0) = swap12 r ∧
    sgn (pSand r (triHalf n r 0) (triHalf n r 1) * pSand r (triHalf n r 1) (triHalf n r 2) *
      pSand r (triHalf n r 2) (triHalf n r 0)) = 1

/-- §5 (after Lemma 5.2): `e_{I₀} e_{I₁} e_{I₂} e_{I₀}` has coordinates
`(I₀, p_{I₀I₁} p_{I₁I₂} p_{I₂I₀}, I₀)`, an odd element of the group `𝓗`-class of `e_{I₀}`. -/
def TriangleProduct : Prop :=
  ∀ n r : ℕ, (r = 2 ∨ r = 3) → r + 2 ≤ n → n % 2 = r % 2 →
    let e : Fin 3 → Pt n → Pt n := fun j => eDiag (triHalf n r j)
    let x := dmul (dmul (dmul (e 0) (e 1)) (e 2)) (e 0)
    x ∈ Jr Fam.B n r ∧ topHalf x = triHalf n r 0 ∧ botHalf x = triHalf n r 0 ∧
      gCoord r x = pSand r (triHalf n r 0) (triHalf n r 1) * pSand r (triHalf n r 1) (triHalf n r 2) *
        pSand r (triHalf n r 2) (triHalf n r 0) ∧
      sgn (gCoord r x) = 1

/-- **Lemma 5.3 (joining two fibres)**: if `F ≠ F'` are `r`-subsets with `r + 2|F \ F'| ≤ n`,
there are `v ∈ H_F`, `w ∈ H_{F'}` with `v ∼ w` (for `B_n`, `r ≤ n`, `r ≡ n (mod 2)`). -/
def Lemma53 : Prop :=
  ∀ n r : ℕ, r ≤ n → n % 2 = r % 2 → ∀ F F' : Finset (Fin n), F.card = r → F'.card = r →
    F ≠ F' → r + 2 * (F \ F').card ≤ n →
      ∃ v ∈ Hr Fam.B n r, ∃ w ∈ Hr Fam.B n r, v.1 = F ∧ w.1 = F' ∧ Compat v w

/-- **Lemma 5.4 (matching)**: if `n - r ≥ 4` and `C(n,r)` is odd, `H \ {I₀, I₁, I₂}` can be
partitioned into pairs `{v, w}` with `v ∼ w` (a fixed-point-free involution `δ` with `v ∼ δ v`). -/
def Lemma54 : Prop :=
  ∀ n r : ℕ, (r = 2 ∨ r = 3) → r < n → n % 2 = r % 2 → 4 ≤ n - r → Odd (n.choose r) →
    ∃ δ : Half n → Half n,
      ∀ v ∈ Hr Fam.B n r \ {triHalf n r 0, triHalf n r 1, triHalf n r 2},
        δ v ∈ Hr Fam.B n r \ {triHalf n r 0, triHalf n r 1, triHalf n r 2} ∧
          δ (δ v) = v ∧ δ v ≠ v ∧ Compat v (δ v)

/-- **Lemma 6.1**: `a(k)` is even for `k ≥ 2`; hence for `n ≥ 4`, `r ∈ {2,3}`, `r < n`,
`N = C(n,r) a(n-r) = |H_r(PB_n)|` is even. -/
def Lemma61 : Prop :=
  (∀ k : ℕ, 2 ≤ k → Even (invCount k)) ∧
    ∀ n r : ℕ, 4 ≤ n → (r = 2 ∨ r = 3) → r < n →
      Even (n.choose r * invCount (n - r)) ∧ Even (Hr Fam.PB n r).ncard

open Classical in
/-- **Proposition 6.2**: the rank-2 principal factor of `PB_3` is isomorphic to
`B(S₂, 3) = M⁰(S₂, [3], [3], Δ₃)` and has no complete mapping. -/
def Prop62 : Prop :=
  MagmaIso (pfMul dmul (Jr Fam.PB 3 2)) (rees0Mul delta3) ∧ ¬ PFHasCM dmul (Jr Fam.PB 3 2)

open Classical in
/-- **Theorem 1.1 (a)**: every proper principal factor of `B_n` has a complete mapping. -/
def Thm11a : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ x ∈ B n, ¬ JRel dmul (B n) x (idD n) →
    PFHasCM dmul (JClass dmul (B n) x)

open Classical in
/-- **Theorem 1.1 (b)**: every proper principal factor of `PB_n` has a complete mapping, except
the rank-2 factor of `PB_3`, which is isomorphic to `B(S₂, 3)` and has none. -/
def Thm11b : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ x ∈ PB n, ¬ JRel dmul (PB n) x (idD n) →
    (PFHasCM dmul (JClass dmul (PB n) x) ↔ ¬ (n = 3 ∧ rank x = 2)) ∧
    (n = 3 → rank x = 2 → MagmaIso (pfMul dmul (JClass dmul (PB n) x)) (rees0Mul delta3))

/-- **Theorem 1.1 (c)**: (i) `B_n` has a complete mapping ⟺ (ii) `PB_n` has one ⟺ (iii) `S_n` has
one ⟺ (iv) `n = 1` or `n ≥ 4`. -/
def Thm11c : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (SubsetHasCM dmul (B n) ↔ SubsetHasCM dmul (PB n)) ∧
    (SubsetHasCM dmul (PB n) ↔ HasCM (Sym n)) ∧
    (HasCM (Sym n) ↔ (n = 1 ∨ 4 ≤ n))

end BackfillPaper5.Challenge
