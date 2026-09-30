import Mathlib

/-!
# Paper 8, trees of diameter at most 4: distances and a centre

Facts about distances in a tree `G` (Mathlib's `SimpleGraph.IsTree`): a vertex on a shortest walk
splits the distance; a path has length equal to the distance of its ends; two neighbours of `x`
that are one step closer to `c` than `x` coincide; if `c ~ c'`, a vertex on the side of `c` and a
vertex on the side of `c'` are joined through the edge `cc'`. Main result: in a finite tree with
all distances at most `4`, a vertex of minimum eccentricity is within distance `2` of every vertex.
This gives the body of the statement `DiamRadius` (`diamRadius`).
-/

set_option autoImplicit false

namespace P8Tree

open SimpleGraph

section Metric

variable {V : Type*} {G : SimpleGraph V}

/-- A vertex `z` on a shortest walk from `u` to `v` splits the distance. -/
theorem dist_split {u v z : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (hz : z ∈ p.support) : G.dist u z + G.dist z v ≤ G.dist u v := by
  obtain ⟨q, r, rfl⟩ := Walk.mem_support_iff_exists_append.1 hz
  have h1 := dist_le q
  have h2 := dist_le r
  rw [Walk.length_append] at hp
  omega

/-- In an acyclic graph the length of a path is the distance between its ends. -/
theorem length_eq_dist_of_isPath (hG : G.IsAcyclic) {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq, hql⟩ := p.reachable.exists_path_of_dist
  have h := (hG.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩
  rw [← hql]
  exact congrArg (fun r : G.Path u v => r.1.length) h

/-- Parent uniqueness in a tree: two neighbours of `x` that are one step closer to `c` than `x`
coincide. -/
theorem eq_of_adj_of_dist_succ (hG : G.IsTree) {c x y₁ y₂ : V} (h₁ : G.Adj y₁ x)
    (h₂ : G.Adj y₂ x) (hd₁ : G.dist c x = G.dist c y₁ + 1)
    (hd₂ : G.dist c x = G.dist c y₂ + 1) : y₁ = y₂ := by
  obtain ⟨q, hq, -⟩ := (hG.connected c x).exists_path_of_dist
  have key : ∀ y, G.Adj y x → G.dist c x = G.dist c y + 1 → y = q.penultimate := by
    intro y hy hdy
    obtain ⟨p, hp, hpl⟩ := (hG.connected c y).exists_path_of_dist
    have hmem : y ∈ q.support := by
      by_contra hn
      have hx := hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hy hn
      have := dist_split p hpl hx
      omega
    exact hG.isAcyclic.eq_penultimate_of_adj_end hq hy.symm hmem
  rw [key y₁ h₁ hd₁, key y₂ h₂ hd₂]

/-- Crossing an edge of a tree: if `c ~ c'`, `x` is farther from `c'` than from `c` and `w` is
farther from `c` than from `c'`, then `d(x, w) = d(x, c) + 1 + d(c', w)`. -/
theorem dist_across (hG : G.IsTree) {c c' x w : V} (hadj : G.Adj c c')
    (hx : G.dist c' x = G.dist c x + 1) (hw : G.dist c w = G.dist c' w + 1) :
    G.dist x w = G.dist x c + 1 + G.dist c' w := by
  obtain ⟨p, hp, hpl⟩ := (hG.connected x c).exists_path_of_dist
  obtain ⟨q, hq, hql⟩ := (hG.connected c' w).exists_path_of_dist
  have hW : (p.append (Walk.cons hadj q)).IsPath := by
    rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons,
      List.nodup_append]
    refine ⟨hp.support_nodup, hq.support_nodup, ?_⟩
    intro z hzp z' hzq hzz
    subst hzz
    have s1 := dist_split p hpl hzp
    have s2 := dist_split q hql hzq
    have t1 : G.dist c w ≤ G.dist c z + G.dist z w := hG.connected.dist_triangle
    have t2 : G.dist c' x ≤ G.dist c' z + G.dist z x := hG.connected.dist_triangle
    have e1 : G.dist c z = G.dist z c := dist_comm
    have e2 : G.dist c' z = G.dist z c' := dist_comm
    have e3 : G.dist z x = G.dist x z := dist_comm
    have e4 : G.dist x c = G.dist c x := dist_comm
    rcases hG.dist_eq_dist_add_one_of_adj z hadj with h | h <;> omega
  have hlen := length_eq_dist_of_isPath hG.isAcyclic _ hW
  rw [Walk.length_append, Walk.length_cons, hpl, hql] at hlen
  omega

/-- In a finite tree with all distances at most `4` some vertex is within distance `2` of every
vertex (a vertex of minimum eccentricity). -/
theorem exists_centre [Fintype V] (hG : G.IsTree) (hd : ∀ u v, G.dist u v ≤ 4) :
    ∃ c, ∀ w, G.dist c w ≤ 2 := by
  have hne : (Finset.univ : Finset V).Nonempty :=
    Finset.univ_nonempty_iff.2 hG.connected.nonempty
  let ecc : V → ℕ := fun u => Finset.univ.sup fun w => G.dist u w
  obtain ⟨c, -, hc⟩ := Finset.exists_min_image Finset.univ ecc hne
  refine ⟨c, fun w => ?_⟩
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_mem_eq_sup Finset.univ hne fun w => G.dist c w
  have hle : ∀ v, G.dist c v ≤ G.dist c w₀ := by
    intro v
    have := Finset.le_sup (f := fun w => G.dist c w) (Finset.mem_univ v)
    rw [hw₀] at this
    exact this
  by_contra hlt
  push Not at hlt
  have h3 : 3 ≤ G.dist c w₀ := by
    have := hle w
    omega
  obtain ⟨p, hpl⟩ := (hG.connected c w₀).exists_walk_length_eq_dist
  cases p with
  | nil => simp at h3
  | @cons _ c' _ hadj q =>
    have hq1 : G.dist c' w₀ ≤ q.length := dist_le q
    have hq2 : G.dist c w₀ ≤ G.dist c c' + G.dist c' w₀ := hG.connected.dist_triangle
    have hcc : G.dist c c' = 1 := dist_eq_one_iff_adj.2 hadj
    rw [Walk.length_cons] at hpl
    have hw : G.dist c w₀ = G.dist c' w₀ + 1 := by omega
    obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup Finset.univ hne fun v => G.dist c' v
    have hmin : ecc c ≤ ecc c' := hc c' (Finset.mem_univ _)
    have hex : G.dist c w₀ ≤ G.dist c' x := by
      have e1 : ecc c = G.dist c w₀ := hw₀
      have e2 : ecc c' = G.dist c' x := hx
      omega
    have hcx : G.dist c x ≤ G.dist c w₀ := hle x
    have e1 : G.dist x c = G.dist c x := dist_comm
    have e2 : G.dist x c' = G.dist c' x := dist_comm
    have h4 := hd x w₀
    rcases hG.dist_eq_dist_add_one_of_adj x hadj with h | h
    · omega
    · rw [e1, e2] at h
      have key := dist_across hG hadj h hw
      omega

/-- From `ediam ≤ 4` to a bound on distances in a connected graph. -/
theorem dist_le_four_of_ediam (hG : G.Connected) (h : G.ediam ≤ 4) (u v : V) :
    G.dist u v ≤ 4 := by
  have h1 : G.edist u v ≤ 4 := le_trans edist_le_ediam h
  rw [← (hG u v).coe_dist_eq_edist] at h1
  exact_mod_cast h1

/-- A finite tree with `ediam ≤ 4` has a vertex within distance `2` of every vertex. -/
theorem exists_centre_of_ediam [Fintype V] (hG : G.IsTree) (h : G.ediam ≤ 4) :
    ∃ c, ∀ w, G.dist c w ≤ 2 :=
  exists_centre hG (dist_le_four_of_ediam hG.connected h)

end Metric

/-- Body of `DiamRadius`: the trees of diameter at most `4` are the trees of radius at most `2`. -/
theorem diamRadius :
    ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree → (T.ediam ≤ 4 ↔ T.radius ≤ 2) := by
  intro V _ T hT
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_centre_of_ediam hT h
    refine le_trans (radius_le_eccent (u := c)) ?_
    rw [eccent_le_iff]
    intro w
    rw [← (hT.connected c w).coe_dist_eq_edist]
    exact_mod_cast hc w
  · intro h
    calc T.ediam ≤ 2 * T.radius := ediam_le_two_mul_radius
      _ ≤ 2 * 2 := by gcongr
      _ = 4 := by norm_num

end P8Tree
