import Research.Backfill.Paper3.Proof.TS.Switch

/-!
# Two isomorphism invariants

`cnDist G a c`: the number of ordered pairs `u ≠ v` with `(u ~ v) = a` and exactly `c` common
neighbours; `triDist G c`: the number of vertices `v` with `tri G v = c`, where `tri G v` is the
number of ordered pairs of adjacent neighbours of `v`. Both are invariant under isomorphism; they
separate the few pairs of 5-regular graphs on 10 vertices with the same `N_{≤t}` profile.
-/

set_option autoImplicit false

namespace P3TS

open Finset

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The number of common neighbours of `u` and `v`. -/
def cn (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  #{w | G.Adj u w ∧ G.Adj v w}

/-- Ordered pairs `u ≠ v` with adjacency `a` and `c` common neighbours. -/
def cnDist (G : SimpleGraph V) [DecidableRel G.Adj] (a : Bool) (c : ℕ) : ℕ :=
  #{p : V × V | p.1 ≠ p.2 ∧ (G.Adj p.1 p.2 ↔ a = true) ∧ cn G p.1 p.2 = c}

/-- Ordered pairs of adjacent neighbours of `v` (twice the number of triangles at `v`). -/
def tri (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  #{p : V × V | G.Adj v p.1 ∧ G.Adj v p.2 ∧ G.Adj p.1 p.2}

/-- Vertices `v` with `tri G v = c`. -/
def triDist (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) : ℕ :=
  #{v | tri G v = c}

variable {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

omit [DecidableEq V] [DecidableEq W] in
theorem cn_iso (φ : G ≃g H) (u v : V) : cn H (φ u) (φ v) = cn G u v := by
  unfold cn
  symm
  apply card_equiv φ.toEquiv
  intro w
  simp only [mem_filter, mem_univ, true_and]
  exact (and_congr φ.map_adj_iff φ.map_adj_iff).symm

theorem cnDist_iso (φ : G ≃g H) (a : Bool) (c : ℕ) : cnDist G a c = cnDist H a c := by
  unfold cnDist
  apply card_equiv (φ.toEquiv.prodCongr φ.toEquiv)
  intro p
  simp only [mem_filter, mem_univ, true_and, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  change _ ↔ φ p.1 ≠ φ p.2 ∧ (H.Adj (φ p.1) (φ p.2) ↔ a = true) ∧ cn H (φ p.1) (φ p.2) = c
  rw [φ.injective.ne_iff, φ.map_adj_iff, cn_iso]

omit [DecidableEq V] [DecidableEq W] in
theorem tri_iso (φ : G ≃g H) (v : V) : tri H (φ v) = tri G v := by
  unfold tri
  symm
  apply card_equiv (φ.toEquiv.prodCongr φ.toEquiv)
  intro p
  simp only [mem_filter, mem_univ, true_and, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  change _ ↔ H.Adj (φ v) (φ p.1) ∧ H.Adj (φ v) (φ p.2) ∧ H.Adj (φ p.1) (φ p.2)
  rw [φ.map_adj_iff, φ.map_adj_iff, φ.map_adj_iff]

omit [DecidableEq V] [DecidableEq W] in
theorem triDist_iso (φ : G ≃g H) (c : ℕ) : triDist G c = triDist H c := by
  unfold triDist
  apply card_equiv φ.toEquiv
  intro v
  simp only [mem_filter, mem_univ, true_and]
  change _ ↔ tri H (φ v) = c
  rw [tri_iso]

end P3TS
