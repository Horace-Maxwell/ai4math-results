import Research.TaskH.Five.FiveLightEdge

/-! Actual shortest two-color paths in a deleted critical edge graph. -/

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

theorem light_swap_pow_apply (a b : Fin 5) (n : ℕ) :
    ((Equiv.swap a b) ^ n) a = if n % 2 = 0 then a else b := by
  have hsq : (Equiv.swap a b) ^ 2 = 1 := by simp [pow_two]
  have hp := pow_eq_pow_mod n hsq
  rw [hp]
  by_cases he : n % 2 = 0
  · simp [he]
  · have ho : n % 2 = 1 := by omega
    simp [ho]

theorem light_follows_drop {α : Type*} {u v : V} (p : G.Walk u v)
    (c : V → α) (σ : Equiv.Perm α) (hf : Follows p c σ) (n : ℕ) :
    Follows (p.drop n) c σ := by
  intro d hd
  rw [Walk.darts_drop] at hd
  exact hf d (List.mem_of_mem_drop hd)

theorem light_follows_take {α : Type*} {u v : V} (p : G.Walk u v)
    (c : V → α) (σ : Equiv.Perm α) (hf : Follows p c σ) (n : ℕ) :
    Follows (p.take n) c σ := by
  intro d hd
  rw [Walk.darts_take] at hd
  exact hf d (List.mem_of_mem_take hd)

theorem light_swap_color_at {u v : V} (p : G.Walk u v) (c : V → Fin 5)
    (b : Fin 5) (hf : Follows p c (Equiv.swap (c u) b))
    (n : ℕ) (hn : n ≤ p.length) :
    c (p.getVert n) = if n % 2 = 0 then c u else b := by
  rw [TaskH.follows_getVert p c (Equiv.swap (c u) b) hf n hn,
    light_swap_pow_apply]

theorem critical_exists_shortest_two_color_path
    (hcrit : IsCriticalPlus 5 G) {u v : V} (huv : G.Adj u v)
    (c : (G.deleteEdges {s(u, v)}).Coloring (Fin 5))
    (b : Fin 5) (hb : b ≠ c u) :
    ∃ p : (G.deleteEdges {s(u, v)}).Walk u v,
      p.IsPath ∧ Follows p c (Equiv.swap (c u) b) ∧
      (∀ q : (G.deleteEdges {s(u, v)}).Walk u v,
        Follows q c (Equiv.swap (c u) b) → p.length ≤ q.length) ∧
      0 < p.length ∧ p.length % 2 = 0 := by
  classical
  have hchange : Equiv.swap (c u) b (c u) ≠ c u := by simpa using hb
  have hreach := TaskH.critical_edge_reachable hcrit c (Equiv.swap (c u) b) hchange
  have hex := TaskH.reach_exists_follows_walk c (Equiv.swap (c u) b) hreach
  obtain ⟨p, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun p : (G.deleteEdges {s(u, v)}).Walk u v => Follows p c (Equiv.swap (c u) b))
    Walk.length hex
  have hbp : p.bypass = p :=
    (Walk.length_le_bypass_length_iff p).mp
      (hmin.le (TaskH.follows_bypass p c (Equiv.swap (c u) b) hmin.1))
  have hpath : p.IsPath := hbp ▸ p.bypass_isPath
  have hpos : 0 < p.length :=
    Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne huv.ne)
  have hcolor := light_swap_color_at p c b hmin.1 p.length (le_refl _)
  rw [Walk.getVert_length] at hcolor
  have he : p.length % 2 = 0 := by
    by_contra hodd
    rw [ite_eq_right hodd] at hcolor
    exact hb (hcolor.symm.trans (TaskH.deletedEdge_coloring_endpoints hcrit c).symm)
  exact ⟨p, hpath, hmin.1, fun q hq => hmin.le hq, hpos, he⟩

/-- A shortest two-color path has no later neighbor of its start in the
other color. The first such point is exactly position one. -/
theorem light_shortest_neighbor_at_start {u v : V} (p : G.Walk u v)
    (c : V → Fin 5) (b : Fin 5) (hb : b ≠ c u)
    (hf : Follows p c (Equiv.swap (c u) b))
    (hmin : ∀ q : G.Walk u v, Follows q c (Equiv.swap (c u) b) →
      p.length ≤ q.length)
    (n : ℕ) (hn : n ≤ p.length) (hc : c (p.getVert n) = b)
    (ha : G.Adj u (p.getVert n)) : n = 1 := by
  let q : G.Walk u v := .cons ha (p.drop n)
  have hq : Follows q c (Equiv.swap (c u) b) := by
    apply (follows_cons ha (p.drop n) c (Equiv.swap (c u) b)).mpr
    exact ⟨by simpa using hc, light_follows_drop p c _ hf n⟩
  have hle := hmin q hq
  have hlen : q.length = 1 + (p.length - n) := by
    simp [q, Walk.length_cons, Walk.drop_length, Nat.add_comm]
  have hnonzero : n ≠ 0 := by
    intro he
    subst n
    simp only [Walk.getVert_zero] at hc
    exact hb hc.symm
  omega

/-- The endpoint version of the same shortest-path shortcut argument. -/
theorem light_shortest_neighbor_at_end {u v : V} (p : G.Walk u v)
    (c : V → Fin 5) (b : Fin 5) (hb : b ≠ c u) (huv : c u = c v)
    (hf : Follows p c (Equiv.swap (c u) b))
    (hmin : ∀ q : G.Walk u v, Follows q c (Equiv.swap (c u) b) →
      p.length ≤ q.length)
    (n : ℕ) (hn : n ≤ p.length) (hc : c (p.getVert n) = b)
    (ha : G.Adj (p.getVert n) v) : n + 1 = p.length := by
  let q : G.Walk u v := (p.take n).append (.cons ha .nil)
  have hq : Follows q c (Equiv.swap (c u) b) := by
    apply (follows_append (p.take n) (.cons ha .nil) c (Equiv.swap (c u) b)).mpr
    refine ⟨light_follows_take p c _ hf n, ?_⟩
    apply (follows_cons ha .nil c (Equiv.swap (c u) b)).mpr
    exact ⟨by rw [hc, Equiv.swap_apply_right, huv], follows_nil _ _ _⟩
  have hle := hmin q hq
  have hlen : q.length = n + 1 := by
    simp [q, Walk.length_append, Walk.take_length, Nat.min_eq_left hn]
  have hnotlast : n ≠ p.length := by
    intro he
    rw [he, Walk.getVert_length, ← huv] at hc
    exact hb hc.symm
  omega

end TaskH.Five

#print axioms TaskH.Five.light_swap_pow_apply
#print axioms TaskH.Five.light_follows_drop
#print axioms TaskH.Five.light_follows_take
#print axioms TaskH.Five.light_swap_color_at
#print axioms TaskH.Five.critical_exists_shortest_two_color_path
#print axioms TaskH.Five.light_shortest_neighbor_at_start
#print axioms TaskH.Five.light_shortest_neighbor_at_end
