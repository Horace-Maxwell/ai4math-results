import Research.TaskH.General.SingletonEdgeOriginal

/-!
A prescribed-order supplying cycle from one actual singleton retains any
second singleton of a different color. The alternate whole deleted-vertex
coloring is constructed internally and R is invoked only after its original
criticality/count proof. This closes a real source bridge toward donor paths;
ordered-list path extraction and the locked-row minimum-degree assembly are
not asserted here.
-/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def singletonCenterDeletedColoring {v a : V} (hva : G.Adj v a)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a) :
    (G.induce {z | z ≠ a}).Coloring (Fin k) := by
  classical
  let f : (G.induce {z | z ≠ a}) →g G.deleteEdges {s(v, a)} :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨hxy, ?_⟩
        intro he
        have heq : s(x.val, y.val) = s(v, a) := Set.mem_singleton_iff.mp he
        have hp : (x.val = v ∧ y.val = a) ∨ (x.val = a ∧ y.val = v) := by
          simpa only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] using heq
        rcases hp with ⟨_, hy⟩ | ⟨hx, _⟩
        · exact y.property hy
        · exact x.property hx }
  exact (singletonEdgeColoring hva c hunique).comap f

omit [Fintype V] in
theorem singletonCenterDeletedColoring_root {v a : V} (hva : G.Adj v a)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a) :
    singletonCenterDeletedColoring hva c hunique ⟨v, hva.ne⟩ = c ⟨a, hva.ne.symm⟩ := by
  change singletonEdgeColoring hva c hunique v = _
  exact singletonEdgeColoring_root hva c hunique

omit [Fintype V] in
theorem singletonCenterDeletedColoring_outside {v a : V} (hva : G.Adj v a)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (hunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (z : V) (hzv : z ≠ v) (hza : z ≠ a) :
    singletonCenterDeletedColoring hva c hunique ⟨z, hza⟩ = c ⟨z, hzv⟩ := by
  change singletonEdgeColoring hva c hunique z = _
  exact singletonEdgeColoring_outside hva c hunique z hzv

theorem equality_singleton_ordered_cycle_retains_other (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (π : Equiv.Perm (Fin k))
    (q : G.Walk v v) (hq : q.IsCycle) (hql : q.length = k)
    (hqf : Follows q (fun z => π (singletonEdgeColoring hva c haunique z)) (finRotate k)) :
    b ∈ q.support := by
  classical
  by_contra hbq
  obtain ⟨i, hi⟩ := rotate_orbit_surjective (by omega)
    (π (singletonEdgeColoring hva c haunique v)) (π (c ⟨b, hvb.ne.symm⟩))
  have hwalk := _root_.TaskH.follows_getVert q
    (fun z => π (singletonEdgeColoring hva c haunique z)) (finRotate k) hqf
    i.val (by have := i.isLt; omega)
  have hcolor : singletonEdgeColoring hva c haunique (q.getVert i.val) =
      c ⟨b, hvb.ne.symm⟩ := π.injective (hwalk.trans hi)
  let z := q.getVert i.val
  have hzv : z ≠ v := by
    intro he
    have hr := singletonEdgeColoring_root hva c haunique
    apply habcolor
    calc
      c ⟨a, hva.ne.symm⟩ = singletonEdgeColoring hva c haunique v := hr.symm
      _ = singletonEdgeColoring hva c haunique z := congrArg _ he.symm
      _ = c ⟨b, hvb.ne.symm⟩ := hcolor
  have hzb : z ≠ b := by
    intro he
    apply hbq
    have hm : z ∈ q.support := q.getVert_mem_support i.val
    rwa [he] at hm
  have hzcolor : c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ :=
    (singletonEdgeColoring_outside hva c haunique z hzv).symm.trans hcolor
  let d := singletonCenterDeletedColoring hvb c hbunique
  have hd : d ⟨z, hzb⟩ = d ⟨v, hvb.ne⟩ := by
    change singletonCenterDeletedColoring hvb c hbunique ⟨z, hzb⟩ =
      singletonCenterDeletedColoring hvb c hbunique ⟨v, hvb.ne⟩
    rw [singletonCenterDeletedColoring_outside hvb c hbunique z hzv hzb,
      singletonCenterDeletedColoring_root hvb c hbunique]
    exact hzcolor
  have he := equality_original_cycle_support_rainbow hk hcrit hcount d q hq hql
    (q.getVert_mem_support i.val) q.start_mem_support hzb hvb.ne hd
  exact hzv he

theorem equality_original_two_singleton_supply (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (π : Equiv.Perm (Fin k)) :
    ∃ q : G.Walk v v, q.IsCycle ∧ q.length = k ∧
      Follows q (fun z => π (singletonEdgeColoring hva c haunique z)) (finRotate k) ∧
      a ∉ q.support ∧ b ∈ q.support := by
  obtain ⟨q, hq, hql, hqf, ha, _⟩ := equality_original_singleton_ordered_cycle
    hk hcrit hcount hva c haunique π
  exact ⟨q, hq, hql, hqf, ha,
    equality_singleton_ordered_cycle_retains_other hk hcrit hcount hva hvb c haunique
      hbunique habcolor π q hq hql hqf⟩

theorem equality_original_singleton_supply_path (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (π : Equiv.Perm (Fin k)) :
    ∃ p : G.Walk v b, p.IsPath ∧ 0 < p.length ∧ p.length < k ∧ a ∉ p.support ∧
      ∀ n : ℕ, n ≤ p.length →
        π (singletonEdgeColoring hva c haunique (p.getVert n)) =
          ((finRotate k) ^ n) (π (c ⟨a, hva.ne.symm⟩)) := by
  classical
  obtain ⟨q, hq, hql, hqf, ha, hb⟩ := equality_original_two_singleton_supply
    hk hcrit hcount hva hvb c haunique hbunique habcolor π
  let p := q.takeUntil b hb
  have hpath : p.IsPath := hq.isPath_takeUntil hb
  have hpos : 0 < p.length :=
    Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hvb.ne)
  have hlt : p.length < k := by
    have hh := q.length_takeUntil_lt_length hb hvb.ne.symm
    simpa only [hql] using hh
  refine ⟨p, hpath, hpos, hlt, ?_, ?_⟩
  · intro hap
    exact ha (q.support_takeUntil_subset_support hb hap)
  · intro n hn
    have hh := _root_.TaskH.follows_getVert q
      (fun z => π (singletonEdgeColoring hva c haunique z)) (finRotate k) hqf n
      (hn.trans (q.length_takeUntil_le_length hb))
    rw [← q.getVert_takeUntil hb hn] at hh
    rw [singletonEdgeColoring_root hva c haunique] at hh
    exact hh

/-- The position of the second singleton in the chosen cyclic color order
determines the actual donor length, not an assumed path-family length. -/
theorem equality_original_singleton_ranked_donor (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (haunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨a, hva.ne.symm⟩ → z = a)
    (hbunique : ∀ (z : V) (hzv : z ≠ v), G.Adj v z →
      c ⟨z, hzv⟩ = c ⟨b, hvb.ne.symm⟩ → z = b)
    (habcolor : c ⟨a, hva.ne.symm⟩ ≠ c ⟨b, hvb.ne.symm⟩)
    (π : Equiv.Perm (Fin k)) (t : ℕ) (ht : t < k)
    (hrank : ((finRotate k) ^ t) (π (c ⟨a, hva.ne.symm⟩)) =
      π (c ⟨b, hvb.ne.symm⟩)) :
    ∃ p : G.Walk v b, p.IsPath ∧ p.length = t ∧ 0 < p.length ∧ a ∉ p.support ∧
      ∀ n : ℕ, 0 < n → n ≤ p.length →
        ∃ hz : p.getVert n ≠ v, π (c ⟨p.getVert n, hz⟩) =
          ((finRotate k) ^ n) (π (c ⟨a, hva.ne.symm⟩)) := by
  obtain ⟨p, hp, hpos, hlt, ha, hword⟩ := equality_original_singleton_supply_path
    hk hcrit hcount hva hvb c haunique hbunique habcolor π
  have hend := hword p.length le_rfl
  rw [Walk.getVert_length, singletonEdgeColoring_outside hva c haunique b hvb.ne.symm] at hend
  have he : p.length = t := GoodCycles.rotate_pow_injective_below (by omega)
    (π (c ⟨a, hva.ne.symm⟩)) hlt ht (hend.symm.trans hrank.symm)
  refine ⟨p, hp, he, hpos, ha, ?_⟩
  intro n hn0 hn
  have hz : p.getVert n ≠ v := by
    intro hh
    have hzero : p.getVert n = p.getVert 0 := by simpa only [Walk.getVert_zero] using hh
    have heN := hp.getVert_injOn (by change n ≤ p.length; exact hn)
      (by change 0 ≤ p.length; omega) hzero
    omega
  refine ⟨hz, ?_⟩
  have hw := hword n hn
  rw [singletonEdgeColoring_outside hva c haunique (p.getVert n) hz] at hw
  exact hw

end TaskH.General

#print axioms TaskH.General.singletonCenterDeletedColoring
#print axioms TaskH.General.singletonCenterDeletedColoring_root
#print axioms TaskH.General.singletonCenterDeletedColoring_outside
#print axioms TaskH.General.equality_singleton_ordered_cycle_retains_other
#print axioms TaskH.General.equality_original_two_singleton_supply
#print axioms TaskH.General.equality_original_singleton_supply_path
#print axioms TaskH.General.equality_original_singleton_ranked_donor
