import Research.TaskH.DirectedCycle
import Research.TaskH.EdgeCycles

/-! Actual two-color components and shortest paths.  These constructions work
in the actual graph supplied as G, in particular the actual deleted-root graph.
There is no assumed path, coverage, or finite pool in the definitions. -/

set_option autoImplicit false
universe u v
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} {A : Type v} [DecidableEq A] {G : SimpleGraph V}

def twoColorComponent (c : G.Coloring A) (alpha beta : A) (a : V) : Set V :=
  {z | Relation.ReflTransGen (ColorStep G c (Equiv.swap alpha beta)) a z}

theorem twoColorComponent_closed (c : G.Coloring A) (alpha beta : A) (a : V)
    {x y : V} (hx : x ∈ twoColorComponent c alpha beta a)
    (hxy : ColorStep G c (Equiv.swap alpha beta) x y) :
    y ∈ twoColorComponent c alpha beta a :=
  hx.tail hxy

noncomputable def twoColorSwap (c : G.Coloring A) (alpha beta : A) (a : V) :
    G.Coloring A :=
  recolorClosed c (Equiv.swap alpha beta) (twoColorComponent c alpha beta a)
    (fun {x y : V} hx hxy =>
      twoColorComponent_closed c alpha beta a (x := x) (y := y) hx hxy)

theorem twoColorSwap_apply (c : G.Coloring A) (alpha beta : A) (a z : V) :
    twoColorSwap c alpha beta a z =
      if z ∈ twoColorComponent c alpha beta a then Equiv.swap alpha beta (c z)
      else c z := by
  classical
  rfl

theorem twoColorSwap_at_start (c : G.Coloring A) (alpha beta : A) (a : V)
    (ha : c a = alpha) : twoColorSwap c alpha beta a a = beta := by
  classical
  have hm : a ∈ twoColorComponent c alpha beta a := Relation.ReflTransGen.refl
  rw [twoColorSwap_apply, ite_eq_left hm, ha, Equiv.swap_apply_left]

theorem twoColorSwap_outside (c : G.Coloring A) (alpha beta : A) (a z : V)
    (hz : z ∉ twoColorComponent c alpha beta a) :
    twoColorSwap c alpha beta a z = c z := by
  classical
  rw [twoColorSwap_apply, ite_eq_right hz]

theorem twoColorSwap_other_color (c : G.Coloring A) (alpha beta : A) (a z : V)
    (ha : c z ≠ alpha) (hb : c z ≠ beta) :
    twoColorSwap c alpha beta a z = c z := by
  classical
  rw [twoColorSwap_apply]
  split_ifs
  · exact Equiv.swap_apply_of_ne_of_ne ha hb
  · rfl

theorem twoColor_swap_pow (alpha beta : A) (n : ℕ) :
    ((Equiv.swap alpha beta) ^ n) alpha =
      if n % 2 = 0 then alpha else beta := by
  classical
  have hsq : (Equiv.swap alpha beta) ^ 2 = 1 := by simp [pow_two]
  rw [pow_eq_pow_mod n hsq]
  by_cases he : n % 2 = 0
  · simp [he]
  · have ho : n % 2 = 1 := by omega
    simp [ho]

theorem twoColor_color_at {a b : V} (p : G.Walk a b) (c : V → A)
    (beta : A) (hf : Follows p c (Equiv.swap (c a) beta))
    (n : ℕ) (hn : n ≤ p.length) :
    c (p.getVert n) = if n % 2 = 0 then c a else beta := by
  rw [TaskH.follows_getVert p c (Equiv.swap (c a) beta) hf n hn,
    twoColor_swap_pow]

theorem twoColor_follows_drop {a b : V} (p : G.Walk a b) (c : V → A)
    (sigma : Equiv.Perm A) (hf : Follows p c sigma) (n : ℕ) :
    Follows (p.drop n) c sigma := by
  intro d hd
  rw [Walk.darts_drop] at hd
  cases (inferInstance : DecidableEq A) (c d.snd) (sigma (c d.fst)) with
  | isTrue hcolor => exact hcolor
  | isFalse hcolor => exact (hcolor (hf d (List.mem_of_mem_drop hd))).elim

theorem twoColor_exists_shortest {a b : V} (c : G.Coloring A) (beta : A)
    (hb : beta ≠ c a) (hend : c b = beta)
    (hreach : b ∈ twoColorComponent c (c a) beta a) :
    ∃ p : G.Walk a b, p.IsPath ∧ Follows p c (Equiv.swap (c a) beta) ∧
      (∀ q : G.Walk a b, Follows q c (Equiv.swap (c a) beta) →
        p.length ≤ q.length) ∧ 0 < p.length ∧ p.length % 2 = 1 := by
  classical
  have hex := TaskH.reach_exists_follows_walk c (Equiv.swap (c a) beta) hreach
  obtain ⟨p, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun p : G.Walk a b => Follows p c (Equiv.swap (c a) beta)) Walk.length hex
  have hbp : p.bypass = p :=
    (Walk.length_le_bypass_length_iff p).mp
      (hmin.le (TaskH.follows_bypass p c (Equiv.swap (c a) beta) hmin.1))
  have hp : p.IsPath := hbp ▸ p.bypass_isPath
  have hab : a ≠ b := by
    intro he
    subst b
    exact hb hend.symm
  have hpos : 0 < p.length :=
    Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hab)
  have hcolor := twoColor_color_at p c beta hmin.1 p.length (le_refl _)
  rw [Walk.getVert_length, hend] at hcolor
  have hodd : p.length % 2 = 1 := by
    by_contra hn
    have he : p.length % 2 = 0 := by omega
    rw [ite_eq_left he] at hcolor
    exact hb hcolor
  exact ⟨p, hp, hmin.1, fun q hq => hmin.le hq, hpos, hodd⟩

theorem twoColor_shortest_neighbor_at_start {a b : V} (p : G.Walk a b)
    (c : V → A) (beta : A) (hb : beta ≠ c a)
    (hf : Follows p c (Equiv.swap (c a) beta))
    (hmin : ∀ q : G.Walk a b, Follows q c (Equiv.swap (c a) beta) →
      p.length ≤ q.length)
    (n : ℕ) (hn : n ≤ p.length) (hc : c (p.getVert n) = beta)
    (ha : G.Adj a (p.getVert n)) : n = 1 := by
  let q : G.Walk a b := .cons ha (p.drop n)
  have hq : Follows q c (Equiv.swap (c a) beta) := by
    apply (follows_cons ha (p.drop n) c (Equiv.swap (c a) beta)).mpr
    exact ⟨by simpa using hc, twoColor_follows_drop p c _ hf n⟩
  have hle := hmin q hq
  have hlen : q.length = 1 + (p.length - n) := by
    simp [q, Walk.length_cons, Walk.drop_length, Nat.add_comm]
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    simp only [Walk.getVert_zero] at hc
    exact hb hc.symm
  omega

theorem twoColor_odd_path_length_le [Fintype V] {a b : V} (p : G.Walk a b)
    (c : V → A) (beta : A) (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c a) beta))
    (hodd : p.length % 2 = 1) (m : ℕ)
    (hcard : (Finset.univ.filter (fun z : V => c z = c a)).card ≤ m) :
    p.length + 1 ≤ 2 * m := by
  classical
  let C := Finset.univ.filter (fun z : V => c z = c a)
  have hindex (i : Fin (p.length / 2 + 1)) : 2 * i.val ≤ p.length := by omega
  let f : Fin (p.length / 2 + 1) → ↥C := fun i =>
    ⟨p.getVert (2 * i.val), by
      change p.getVert (2 * i.val) ∈ Finset.univ.filter (fun z : V => c z = c a)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using twoColor_color_at p c beta hf (2 * i.val) (hindex i)⟩
  have hinj : Function.Injective f := by
    intro i j he
    have hv : p.getVert (2 * i.val) = p.getVert (2 * j.val) := congrArg Subtype.val he
    have hn := hp.getVert_injOn (by change 2 * i.val ≤ p.length; exact hindex i)
      (by change 2 * j.val ≤ p.length; exact hindex j) hv
    apply Fin.ext
    omega
  have hle := Fintype.card_le_of_injective f hinj
  have hc : p.length / 2 + 1 ≤ C.card := by simpa using hle
  change C.card ≤ m at hcard
  omega

end TaskH.Seven
#print axioms TaskH.Seven.twoColorComponent
#print axioms TaskH.Seven.twoColorComponent_closed
#print axioms TaskH.Seven.twoColorSwap
#print axioms TaskH.Seven.twoColorSwap_apply
#print axioms TaskH.Seven.twoColorSwap_at_start
#print axioms TaskH.Seven.twoColorSwap_outside
#print axioms TaskH.Seven.twoColorSwap_other_color
#print axioms TaskH.Seven.twoColor_swap_pow
#print axioms TaskH.Seven.twoColor_color_at
#print axioms TaskH.Seven.twoColor_follows_drop
#print axioms TaskH.Seven.twoColor_exists_shortest
#print axioms TaskH.Seven.twoColor_shortest_neighbor_at_start
#print axioms TaskH.Seven.twoColor_odd_path_length_le
