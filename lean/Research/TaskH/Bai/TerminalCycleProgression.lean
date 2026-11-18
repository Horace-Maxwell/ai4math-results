import Research.TaskH.Gao.TerminalFragmentExistence
import Research.TaskH.Gao.Challenge
set_option autoImplicit false
universe u
namespace TaskH.Bai
open SimpleGraph TaskH.Gao TaskH.Fan
variable {V : Type u}

/-- Closing a genuine long simple path by its actual endpoint edge gives a real cycle. -/
theorem close_actual_simple_path {G : SimpleGraph V} {x y : V}
    (e : G.Adj x y) (p : G.Walk x y) (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    (Walk.cons e p.reverse).IsCycle := by
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · rw [Walk.tail_cons]
    exact (Walk.isPath_copy p.reverse _ _).mpr hp.reverse
  · change 3 ≤ p.reverse.length + 1
    rw [Walk.length_reverse]
    omega

/-- The original graph internally supplies a terminal block, edge roots and all cycle witnesses. -/
theorem original_terminal_cycle_progression [Fintype V] [Nonempty V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (E1 : RootedPathClaim.{u}) (m t : ℕ) (hm : 2 ≤ m) (ht : 2 ≤ t)
    (htm : t + 1 ≤ m) (hG : G.Connected) (hdeg : ∀ v : V, m ≤ G.degree v) :
    ∃ (A d : ℕ) (z : V) (f : Fin t → G.Walk z z),
      3 ≤ A ∧ (d = 1 ∨ d = 2) ∧
      ∀ i : Fin t, (f i).IsCycle ∧ (f i).length = A + i.val * d := by
  classical
  let v : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp (by have := hdeg v; omega)
  have nt : Nontrivial V := nontrivial_of_ne v w hvw.ne
  obtain ⟨I, b, hI⟩ := @terminal_fragment_exists V inferInstance nt G hG
  let B : Set V := fragmentBlock I b
  let iB : Fintype B := Fintype.ofFinite B
  let J : SimpleGraph B := G.induce B
  let br : B := ⟨b, Or.inl rfl⟩
  have hTwo : @TwoConnected B iB J := by
    rcases @terminalFragment_dichotomy V inferInstance G I b iB hG hI with hs | htwo
    · obtain ⟨a, he, _hab, _hbridge, _hblock⟩ := hs
      have hsingle : TerminalFragment G {a} b := by simpa only [he] using hI
      have hn := (terminalFragment_singleton_bridge G a b hG hsingle).2.2.1
      have hda : G.degree a = 1 := by
        rw [← G.ncard_neighborSet, hn, Set.ncard_singleton]
      have hma : 2 ≤ G.degree a := hm.trans (hdeg a)
      have hbad : (2 : ℕ) ≤ 1 := Eq.mp (congrArg (fun n : ℕ => 2 ≤ n) hda) hma
      exact False.elim (Nat.not_add_one_le_self 1 hbad)
    · exact htwo
  obtain ⟨a, ha⟩ := hI.1
  let ar : B := ⟨a, Or.inr ha⟩
  have hba : br ≠ ar := by
    intro he
    have he' : b = a := congrArg Subtype.val he
    exact hI.2.1 (Eq.mp (congrArg (fun z : V => z ∈ I) he'.symm) ha)
  obtain ⟨yr, he⟩ := (hTwo.2.1 br ar).nonempty_neighborSet_left hba
  have e : J.Adj br yr := he
  have hroot : @RootedTwoConnected B iB J br yr := by
    refine ⟨?_, ?_⟩
    · intro h
      subst yr
      exact J.irrefl e
    have hedge : SimpleGraph.edge br yr ≤ J :=
      (SimpleGraph.edge_le_iff (G := J)).mpr (Or.inr e)
    have hs : J ⊔ SimpleGraph.edge br yr = J := sup_eq_left.mpr hedge
    rw [hs]
    exact hTwo
  have hnon : NonrootDegreeAtLeast J br yr (t + 1) := by
    intro z hzb _hzy
    have hzb' : z.val ≠ b := by
      intro he
      exact hzb (Subtype.ext he)
    have heq := rootedSet_neighbor_ncard G B b
      (fragmentBlock_closed G I b hI.2.2.1) z hzb'
    change t + 1 ≤ ((G.induce B).neighborSet z).ncard
    rw [← heq, G.ncard_neighborSet]
    exact htm.trans (hdeg z.val)
  obtain ⟨a0, d, p, hfam⟩ := @E1 t (by omega) B iB J br yr hroot hnon
  rcases hfam with ⟨ha0, hd, hp⟩
  let incl : J →g G := ⟨Subtype.val, fun {a b} h => h⟩
  let f : Fin t → G.Walk b b := fun i => (Walk.cons (G := J) e (p i).reverse).map incl
  refine ⟨a0 + 1, d, b, f, by omega, hd, ?_⟩
  intro i
  have hpi := hp i
  have hplen : 2 ≤ (p i).length := by rw [hpi.2]; omega
  have hcycle := close_actual_simple_path (G := J) e (p i) hpi.1 hplen
  constructor
  · exact (Walk.isCycle_map_iff_of_injective (f := incl) Subtype.val_injective).mpr hcycle
  · change ((Walk.cons (G := J) e (p i).reverse).map incl).length = a0 + 1 + i.val * d
    rw [Walk.length_map, Walk.length_cons, Walk.length_reverse, hpi.2]
    omega

/-- Actual walk induction computes the parity of a proper two-coloring. -/
theorem two_color_walk_parity {G : SimpleGraph V} (c : G.Coloring (Fin 2))
    {x y : V} (p : G.Walk x y) : ((c x).val + p.length) % 2 = (c y).val := by
  induction p with
  | nil => exact Nat.mod_eq_of_lt (c _).isLt
  | @cons a z b e p ih =>
    have hne : (c a).val ≠ (c z).val := fun he => c.valid e (Fin.ext he)
    have ha := (c a).isLt
    have hz := (c z).isLt
    have hb := (c b).isLt
    change ((c a).val + (p.length + 1)) % 2 = (c b).val
    omega

/-- A genuine closed walk in a bipartite graph always has even length. -/
theorem bipartite_closed_walk_even {G : SimpleGraph V} (hbi : G.IsBipartite)
    {z : V} (p : G.Walk z z) : p.length % 2 = 0 := by
  obtain ⟨c⟩ := hbi
  have hh := two_color_walk_parity c p
  have hc := (c z).isLt
  omega

#print axioms close_actual_simple_path
#print axioms original_terminal_cycle_progression
#print axioms two_color_walk_parity
#print axioms bipartite_closed_walk_even
end TaskH.Bai
