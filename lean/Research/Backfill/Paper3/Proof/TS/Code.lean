import Research.Backfill.Paper3.Proof.TS.Switch

/-!
# Graphs on `Fin n` given by adjacency codes; a checker for 2-switch certificates

`ofCode n c` is the graph on `Fin n` whose adjacency matrix is stored in the bits of `c` (bit
`a * n + b`). `chk` walks through the 2-switches of such a graph in canonical form (`u₁` the
smallest of the four vertices) and checks, for each, a certificate `(j, σ, σ⁻¹)` (permutations
packed four bits per vertex) that the switched graph is isomorphic to the graph with code number
`j`. The kernel runs the checker; `closure_of_chk` turns a successful run into isomorphisms.
-/

set_option autoImplicit false

namespace P3TS

open Finset BackfillPaper3.Challenge

/-- `∀ k < n, p k`, as a Boolean. -/
def allLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | k + 1, p => allLt k p && p k

theorem allLt_iff {n : ℕ} {p : ℕ → Bool} : allLt n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    simp only [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩

/-- Bit `a * n + b` of `c`: entry `(a, b)` of the adjacency matrix. -/
def adjB (n c a b : ℕ) : Bool := c.testBit (a * n + b)

/-- The graph on `Fin n` with adjacency matrix `c` (symmetrised, without loops). -/
def ofCode (n c : ℕ) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ (adjB n c a.val b.val = true ∨ adjB n c b.val a.val = true)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (n c : ℕ) : DecidableRel (ofCode n c).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ (adjB n c a.val b.val = true ∨ adjB n c b.val a.val = true)))

/-- The matrix `c` is symmetric and has zero diagonal. -/
def wfB (n c : ℕ) : Bool :=
  allLt n fun a => !adjB n c a a && allLt n fun b => adjB n c a b == adjB n c b a

theorem wfB_spec {n c : ℕ} (h : wfB n c = true) {a b : ℕ} (ha : a < n) (hb : b < n) :
    adjB n c a a = false ∧ adjB n c a b = adjB n c b a := by
  rw [wfB, allLt_iff] at h
  have h' := h a ha
  rw [Bool.and_eq_true, Bool.not_eq_true', allLt_iff] at h'
  exact ⟨h'.1, by simpa using h'.2 b hb⟩

theorem ofCode_adj {n c : ℕ} (h : wfB n c = true) (a b : Fin n) :
    (ofCode n c).Adj a b ↔ adjB n c a.val b.val = true := by
  obtain ⟨h1, h2⟩ := wfB_spec h a.isLt b.isLt
  show a ≠ b ∧ (adjB n c a.val b.val = true ∨ adjB n c b.val a.val = true) ↔ _
  rw [← h2, or_self]
  constructor
  · exact fun h => h.2
  · intro hab
    refine ⟨?_, hab⟩
    rintro rfl
    rw [h1] at hab
    exact Bool.false_ne_true hab

/-- `s(a, b) = s(c, d)`, as a Boolean on natural numbers. -/
def pe (a b c d : ℕ) : Bool := (a == c && b == d) || (a == d && b == c)

theorem pe_iff {n : ℕ} (a b c d : Fin n) :
    pe a.val b.val c.val d.val = true ↔ s(a, b) = s(c, d) := by
  rw [Sym2.eq_iff]
  simp [pe, Fin.val_inj]

/-- Adjacency of the 2-switch `twoSwitch (ofCode n c) u₁ w₁ u₂ w₂` at `a ≠ b`. -/
def swB (n c u₁ w₁ u₂ w₂ a b : ℕ) : Bool :=
  (adjB n c a b && !pe a b u₁ w₁ && !pe a b u₂ w₂) || pe a b u₁ w₂ || pe a b u₂ w₁

theorem twoSwitch_ofCode_adj {n c : ℕ} (h : wfB n c = true) {u₁ w₁ u₂ w₂ a b : Fin n}
    (hab : a ≠ b) :
    (twoSwitch (ofCode n c) u₁ w₁ u₂ w₂).Adj a b ↔
      swB n c u₁.val w₁.val u₂.val w₂.val a.val b.val = true := by
  rw [twoSwitch_adj, ofCode_adj h, ← pe_iff a b u₁ w₁, ← pe_iff a b u₂ w₂, ← pe_iff a b u₁ w₂,
    ← pe_iff a b u₂ w₁]
  simp only [swB, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', ne_eq, hab,
    not_false_eq_true, and_true, Bool.not_eq_true]
  tauto

/-- Image of `a` under the permutation packed in `p` (four bits per vertex). -/
def pim (p a : ℕ) : ℕ := (p >>> (4 * a)) &&& 15

/-- `p` maps `{0, …, n-1}` into itself and `q` undoes it (so `p` is a permutation). -/
def permOK (n p q : ℕ) : Bool :=
  allLt n fun a => decide (pim p a < n) && pim q (pim p a) == a

/-- `p` maps the 2-switch of `c` onto the graph with code `cj` (pairs `a < b`). -/
def isoB (n c u₁ w₁ u₂ w₂ cj p : ℕ) : Bool :=
  allLt n fun b => allLt b fun a => swB n c u₁ w₁ u₂ w₂ a b == adjB n cj (pim p a) (pim p b)

theorem iso_of_check {n c cj p q : ℕ} (hc : wfB n c = true) (hcj : wfB n cj = true)
    (hp : permOK n p q = true) {u₁ w₁ u₂ w₂ : Fin n}
    (hiso : isoB n c u₁.val w₁.val u₂.val w₂.val cj p = true) :
    Nonempty (twoSwitch (ofCode n c) u₁ w₁ u₂ w₂ ≃g ofCode n cj) := by
  rw [permOK, allLt_iff] at hp
  have hp' : ∀ a : Fin n, pim p a.val < n ∧ pim q (pim p a.val) = a.val := by
    intro a
    have := hp a.val a.isLt
    rw [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at this
    exact this
  let σ : Fin n → Fin n := fun a => ⟨pim p a.val, (hp' a).1⟩
  have hσ : Function.Injective σ := by
    intro a b hab
    have hab' : pim p a.val = pim p b.val := congrArg Fin.val hab
    apply Fin.ext
    rw [← (hp' a).2, ← (hp' b).2, hab']
  rw [isoB, allLt_iff] at hiso
  have key : ∀ a b : Fin n, a < b →
      ((twoSwitch (ofCode n c) u₁ w₁ u₂ w₂).Adj a b ↔ (ofCode n cj).Adj (σ a) (σ b)) := by
    intro a b hab
    have h1 := hiso b.val b.isLt
    rw [allLt_iff] at h1
    have h2 := h1 a.val hab
    rw [beq_iff_eq] at h2
    rw [twoSwitch_ofCode_adj hc (ne_of_lt hab), ofCode_adj hcj, h2]
  refine ⟨⟨Equiv.ofBijective σ hσ.bijective_of_finite, ?_⟩⟩
  intro a b
  simp only [Equiv.ofBijective_apply]
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact (key a b hab).symm
  · simp only [SimpleGraph.irrefl]
  · rw [SimpleGraph.adj_comm, (twoSwitch (ofCode n c) u₁ w₁ u₂ w₂).adj_comm]
    exact (key b a hab).symm

/-- The side conditions of a 2-switch of `ofCode n c`, as a Boolean. -/
def validB (n c u₁ w₁ u₂ w₂ : ℕ) : Bool :=
  adjB n c u₁ w₁ && adjB n c u₂ w₂ && !adjB n c u₁ w₂ && !adjB n c u₂ w₁ && u₂ != w₁ && u₁ != w₂

theorem validB_of_isSwitch {n c : ℕ} (h : wfB n c = true) {u₁ w₁ u₂ w₂ : Fin n}
    (hs : IsSwitch (ofCode n c) u₁ w₁ u₂ w₂) : validB n c u₁.val w₁.val u₂.val w₂.val = true := by
  have e1 := (ofCode_adj h u₁ w₁).1 hs.adj₁
  have e2 := (ofCode_adj h u₂ w₂).1 hs.adj₂
  have e3 : adjB n c u₁.val w₂.val = false := by
    rw [← Bool.not_eq_true, ← ofCode_adj h]
    exact hs.nadj₁
  have e4 : adjB n c u₂.val w₁.val = false := by
    rw [← Bool.not_eq_true, ← ofCode_adj h]
    exact hs.nadj₂
  have e5 : u₂.val ≠ w₁.val := fun h' => hs.ne₂ (Fin.ext h')
  have e6 : u₁.val ≠ w₂.val := fun h' => hs.ne₁ (Fin.ext h')
  simp [validB, e1, e2, e3, e4, e5, e6]

/-- The canonical 2-switch positions: `u₁` is the smallest of the four vertices. -/
def tuples (n : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun u₁ => (List.range' (u₁ + 1) (n - u₁ - 1)).flatMap fun w₁ =>
    (List.range' (u₁ + 1) (n - u₁ - 1)).flatMap fun u₂ =>
      (List.range' (u₁ + 1) (n - u₁ - 1)).map fun w₂ => (u₁, w₁, u₂, w₂)

theorem mem_tuples {n u₁ w₁ u₂ w₂ : ℕ} (h1 : u₁ < w₁) (h2 : u₁ < u₂) (h3 : u₁ < w₂)
    (hw₁ : w₁ < n) (hu₂ : u₂ < n) (hw₂ : w₂ < n) : (u₁, w₁, u₂, w₂) ∈ tuples n := by
  simp only [tuples, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_range'_1]
  exact ⟨u₁, by omega, w₁, ⟨by omega, by omega⟩, u₂, ⟨by omega, by omega⟩, w₂,
    ⟨by omega, by omega⟩, rfl⟩

/-- The certificate checker: walks through `ts`; for each valid switch it consumes the next
certificate `(j, p, q)` of `cs`. -/
def chk (n k c : ℕ) (codes : List ℕ) : List (ℕ × ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ) → Bool
  | [], _ => true
  | (u₁, w₁, u₂, w₂) :: ts, cs =>
    if validB n c u₁ w₁ u₂ w₂ then
      match cs with
      | [] => false
      | (j, p, q) :: cs' =>
        decide (j < k) && permOK n p q && isoB n c u₁ w₁ u₂ w₂ (codes.getD j 0) p &&
          chk n k c codes ts cs'
    else chk n k c codes ts cs

theorem chk_sound {n k c : ℕ} {codes : List ℕ} :
    ∀ (ts : List (ℕ × ℕ × ℕ × ℕ)) (cs : List (ℕ × ℕ × ℕ)), chk n k c codes ts cs = true →
      ∀ u₁ w₁ u₂ w₂, (u₁, w₁, u₂, w₂) ∈ ts → validB n c u₁ w₁ u₂ w₂ = true →
        ∃ j p q, j < k ∧ permOK n p q = true ∧ isoB n c u₁ w₁ u₂ w₂ (codes.getD j 0) p = true := by
  intro ts
  induction ts with
  | nil => intro _ _ _ _ _ _ h
           exact absurd h List.not_mem_nil
  | cons x ts ih =>
    obtain ⟨a₁, b₁, a₂, b₂⟩ := x
    intro cs hchk u₁ w₁ u₂ w₂ hmem hv
    simp only [chk] at hchk
    by_cases hva : validB n c a₁ b₁ a₂ b₂ = true
    · rw [ite_eq_left hva] at hchk
      rcases cs with _ | ⟨⟨j, p, q⟩, cs'⟩
      · exact absurd hchk Bool.false_ne_true
      · simp only [Bool.and_eq_true, decide_eq_true_iff] at hchk
        obtain ⟨⟨⟨hj, hp⟩, hi⟩, hrest⟩ := hchk
        rcases List.mem_cons.1 hmem with heq | hmem'
        · simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
          exact ⟨j, p, q, hj, hp, hi⟩
        · exact ih cs' hrest u₁ w₁ u₂ w₂ hmem' hv
    · rw [ite_eq_right hva] at hchk
      rcases List.mem_cons.1 hmem with heq | hmem'
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
        exact absurd hv hva
      · exact ih cs hchk u₁ w₁ u₂ w₂ hmem' hv

/-- A successful run of the checker on the graph with code number `i`: every canonical 2-switch
of it is isomorphic to one of the coded graphs. -/
theorem closure_of_chk {n k : ℕ} {codes : List ℕ}
    (hwf : ∀ j < k, wfB n (codes.getD j 0) = true) {i : ℕ} (hi : i < k)
    {cs : List (ℕ × ℕ × ℕ)} (h : chk n k (codes.getD i 0) codes (tuples n) cs = true)
    (u₁ w₁ u₂ w₂ : Fin n) (h1 : u₁ < w₁) (h2 : u₁ < u₂) (h3 : u₁ < w₂)
    (hs : IsSwitch (ofCode n (codes.getD i 0)) u₁ w₁ u₂ w₂) :
    ∃ j : Fin k, Nonempty (twoSwitch (ofCode n (codes.getD i 0)) u₁ w₁ u₂ w₂ ≃g
      ofCode n (codes.getD j 0)) := by
  have hv := validB_of_isSwitch (hwf i hi) hs
  have hm := mem_tuples (n := n) h1 h2 h3 w₁.isLt u₂.isLt w₂.isLt
  obtain ⟨j, p, q, hj, hp, hiso⟩ := chk_sound _ _ h _ _ _ _ hm hv
  exact ⟨⟨j, hj⟩, iso_of_check (hwf i hi) (hwf j hj) hp hiso⟩

end P3TS
