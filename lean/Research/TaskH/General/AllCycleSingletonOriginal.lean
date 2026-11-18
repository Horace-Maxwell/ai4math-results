import Research.TaskH.General.SingletonRetainedOriginal

/-! ALL actual Ck and cycle-edge-set transport from the original equality.
The fixed whole deleted-root coloring and real singleton neighbors are kept.
No selected rank-order family is counted or supplied as a new premise. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.General.GoodCycles

variable {k : ℕ} {V : Type u} {G : SimpleGraph V}

theorem equality_avoiding_cycle_color_exists [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v x : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (p : G.Walk x x) (hp : p.IsCycle) (hlen : p.length = k)
    (hv : v ∉ p.support) (γ : Fin k) :
    ∃ (z : V) (hzv : z ≠ v), z ∈ p.support ∧ c ⟨z, hzv⟩ = γ := by
  have hinj := equality_avoiding_cycle_word_injective hk hcrit hcount c p hp hlen hv
  obtain ⟨i, hi⟩ := (Finite.surjective_of_injective hinj) γ
  let z := p.getVert i.val
  have hzv : z ≠ v := by
    intro he
    apply hv
    have hm := p.getVert_mem_support i.val
    change z ∈ p.support at hm
    simpa only [he] using hm
  refine ⟨z, hzv, p.getVert_mem_support i.val, ?_⟩
  change c ⟨p.getVert i.val, _⟩ = γ at hi
  exact hi

/-- Every actual Ck through v avoiding its singleton neighbor a omits the
ENTIRE old a-color class. No prescribed order is assumed. -/
theorem equality_singleton_cycle_omits_whole_class [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a x : V} (hva : G.Adj v a)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (p : G.Walk x x) (hp : p.IsCycle) (hlen : p.length = k)
    (hv : v ∈ p.support) (ha : a ∉ p.support) :
    ∀ (z : V) (hzv : z ≠ v), z ∈ p.support →
      c ⟨z, hzv⟩ ≠ c ⟨a, hva.ne.symm⟩ := by
  intro z hzv hzq he
  have hza : z ≠ a := by
    intro hh
    exact ha (Eq.mp (congrArg (fun w : V => w ∈ p.support) hh) hzq)
  let d := singletonCenterDeletedColoring hva c haunique
  have hd : d ⟨z, hza⟩ = d ⟨v, hva.ne⟩ := by
    change singletonCenterDeletedColoring hva c haunique ⟨z, hza⟩ =
      singletonCenterDeletedColoring hva c haunique ⟨v, hva.ne⟩
    rw [singletonCenterDeletedColoring_outside hva c haunique z hzv hza,
      singletonCenterDeletedColoring_root hva c haunique]
    exact he
  have hsame := equality_original_cycle_support_rainbow hk hcrit hcount d p hp hlen
    hzq hv hza hva.ne hd
  exact hzv hsame

/-- ANY original Ck through v and avoiding a retains the other singleton b.
The entire actual cycle has all k colors in the constructed whole G-a coloring. -/
theorem equality_all_cycles_retain_other_singleton [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b x : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (p : G.Walk x x) (hp : p.IsCycle) (hlen : p.length = k)
    (hv : v ∈ p.support) (ha : a ∉ p.support) : b ∈ p.support := by
  by_contra hb
  let d := singletonCenterDeletedColoring hva c haunique
  obtain ⟨z, hza, hzq, hzc⟩ := equality_avoiding_cycle_color_exists
    hk hcrit hcount d p hp hlen ha (c ⟨b, hvb.ne.symm⟩)
  have hzv : z ≠ v := by
    intro he
    apply habcolor
    calc
      c ⟨a, hva.ne.symm⟩ = d ⟨v, hva.ne⟩ :=
        (singletonCenterDeletedColoring_root hva c haunique).symm
      _ = d ⟨z, hza⟩ := congrArg d (Subtype.ext he.symm)
      _ = c ⟨b, hvb.ne.symm⟩ := hzc
  have hzold : c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ :=
    (singletonCenterDeletedColoring_outside hva c haunique z hzv hza).symm.trans hzc
  exact (equality_singleton_cycle_omits_whole_class hk hcrit hcount hvb c hbunique
    p hp hlen hv hb z hzv hzq) hzold

/-- The transport applies to ALL finite unoriented edge sets in the original
E(v,a) family, retaining b and omitting every point of the old whole a-class. -/
theorem equality_all_edge_sets_retain_and_omit [Fintype V] (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (s : Finset (Sym2 V)) (hs : s ∈ _root_.TaskH.modCyclesThroughAvoid k G v a) :
    _root_.TaskH.CycleContains s b ∧
      ∀ (z : V) (hzv : z ≠ v), c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ →
        ¬ _root_.TaskH.CycleContains s z := by
  classical
  obtain ⟨x, p, hp, he, hdiv⟩ := Basics.mem_modCycleEdgeSets_iff.mp hs.1
  have hlen := GoodCycles.equality_shortCycles_from_critical_count hk hcrit hcount p hp hdiv
  have hv : v ∈ p.support := by
    apply (_root_.TaskH.cycleContains_edges_toFinset_iff p hp.not_nil v).mp
    rw [he]
    exact hs.2.1
  have ha : a ∉ p.support := by
    intro haq
    apply hs.2.2
    rw [← he]
    exact (_root_.TaskH.cycleContains_edges_toFinset_iff p hp.not_nil a).mpr haq
  constructor
  · rw [← he]
    exact (_root_.TaskH.cycleContains_edges_toFinset_iff p hp.not_nil b).mpr
      (equality_all_cycles_retain_other_singleton hk hcrit hcount hva hvb c
        haunique hbunique habcolor p hp hlen hv ha)
  · intro z hzv hzc hzs
    have hzq : z ∈ p.support := by
      apply (_root_.TaskH.cycleContains_edges_toFinset_iff p hp.not_nil z).mp
      rw [he]
      exact hzs
    exact (equality_singleton_cycle_omits_whole_class hk hcrit hcount hva c haunique
      p hp hlen hv ha z hzv hzq) hzc

end TaskH.General

#print axioms TaskH.General.equality_avoiding_cycle_color_exists
#print axioms TaskH.General.equality_singleton_cycle_omits_whole_class
#print axioms TaskH.General.equality_all_cycles_retain_other_singleton
#print axioms TaskH.General.equality_all_edge_sets_retain_and_omit
