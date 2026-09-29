import Research.Backfill.Paper4.Challenge

/-!
# Single-source distance rows, and two certificates that a graph is not median

(Written by Claude, 2026-09-28, while Codex was out of quota.) A row `d` certified from a
source `s` (zero only at `s`, a descending neighbour from every other vertex, and the
Lipschitz property along edges) is the true distance from `s`. Rows from `a`, `b` and `c`
determine the three intervals of the triple `a, b, c`; two distinct vertices in all three
intervals, or none, show that the graph is not median.
-/

set_option autoImplicit false

namespace ClaudePaper4

open BackfillPaper4 SimpleGraph

theorem dist_row {V : Type*} (G : SimpleGraph V) (s : V) (d : V → ℕ)
    (hz : ∀ v, d v = 0 → v = s)
    (hstep : ∀ v, d v ≠ 0 → ∃ z, G.Adj v z ∧ d z + 1 = d v)
    (hlip : ∀ u v, G.Adj u v → d u ≤ d v + 1) (hs : d s = 0) :
    ∀ v, G.dist s v = d v := by
  have hwalk : ∀ n : ℕ, ∀ v, d v = n → ∃ p : G.Walk v s, p.length = n := by
    intro n
    induction n with
    | zero =>
      intro v h
      obtain rfl := hz v h
      exact ⟨Walk.nil, rfl⟩
    | succ n ih =>
      intro v h
      obtain ⟨z, hvz, hz'⟩ := hstep v (by omega)
      obtain ⟨p, hp⟩ := ih z (by omega)
      exact ⟨Walk.cons hvz p, by simp [hp]⟩
  have hlow : ∀ x y (p : G.Walk x y), y = s → d x ≤ p.length := by
    intro x y p
    induction p with
    | nil => intro h; subst h; simp [hs]
    | @cons u w t h p ih =>
      intro ht
      have h1 := ih ht
      have h2 := hlip u w h
      simp only [Walk.length_cons]
      omega
  intro v
  rw [SimpleGraph.dist_comm]
  obtain ⟨p, hp⟩ := hwalk _ v rfl
  apply le_antisymm
  · exact (SimpleGraph.dist_le p).trans hp.le
  · have hr : G.Reachable v s := ⟨p⟩
    obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
    exact hq ▸ hlow v s q rfl

/-- The three interval conditions of `x` for the triple `a, b, c`, in terms of the rows. -/
abbrev inAll {V : Type*} (ra rb rc : V → ℕ) (b c x : V) : Prop :=
  ra x + rb x = ra b ∧ ra x + rc x = ra c ∧ rb x + rc x = rb c

theorem inAll_iff {V : Type*} (G : SimpleGraph V) {a b c : V} {ra rb rc : V → ℕ}
    (ha : ∀ v, G.dist a v = ra v) (hb : ∀ v, G.dist b v = rb v) (hc : ∀ v, G.dist c v = rc v)
    (x : V) :
    (Challenge.InInterval G a b x ∧ Challenge.InInterval G a c x ∧
      Challenge.InInterval G b c x) ↔ inAll ra rb rc b c x := by
  simp only [Challenge.InInterval, inAll, SimpleGraph.dist_comm (u := x), ha, hb, hc]

theorem not_median_two {V : Type*} (G : SimpleGraph V) {a b c : V} {ra rb rc : V → ℕ}
    (ha : ∀ v, G.dist a v = ra v) (hb : ∀ v, G.dist b v = rb v) (hc : ∀ v, G.dist c v = rc v)
    (x y : V) (hxy : x ≠ y) (hx : inAll ra rb rc b c x) (hy : inAll ra rb rc b c y) :
    ¬ Challenge.IsMedian G := by
  intro hm
  obtain ⟨z, _, hu⟩ := hm.2 a b c
  exact hxy ((hu x ((inAll_iff G ha hb hc x).mpr hx)).trans
    (hu y ((inAll_iff G ha hb hc y).mpr hy)).symm)

theorem not_median_zero {V : Type*} (G : SimpleGraph V) {a b c : V} {ra rb rc : V → ℕ}
    (ha : ∀ v, G.dist a v = ra v) (hb : ∀ v, G.dist b v = rb v) (hc : ∀ v, G.dist c v = rc v)
    (h0 : ∀ x, ¬ inAll ra rb rc b c x) : ¬ Challenge.IsMedian G := by
  intro hm
  obtain ⟨z, hz, _⟩ := hm.2 a b c
  exact h0 z ((inAll_iff G ha hb hc z).mp hz)

#print axioms dist_row
#print axioms not_median_two
#print axioms not_median_zero

end ClaudePaper4
