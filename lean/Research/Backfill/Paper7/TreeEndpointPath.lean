import Research.Backfill.Paper7.ChallengeV2

/-! Source-only conditional structure helper. A finite connected acyclic
graph of maximum degree at most two is ordered by a genuine spanning path
starting at any specified vertex of degree at most one. Singleton graphs
are included. No covering path, Sun form or spectral conclusion is assumed.
No IntroUnicyclic21 check is supplied. -/
set_option autoImplicit false
noncomputable section
namespace Paper7TreeEndpointPath
open SimpleGraph

theorem neighbors_eq_of_degree_le_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u a b : V)
    (hdeg : G.degree u ≤ 1) (ha : G.Adj u a) (hb : G.Adj u b) : a = b := by
  have hcard : (G.neighborFinset u).card ≤ 1 := hdeg
  exact Finset.card_le_one.mp hcard a ((G.mem_neighborFinset u a).mpr ha)
    b ((G.mem_neighborFinset u b).mpr hb)
#print axioms Paper7TreeEndpointPath.neighbors_eq_of_degree_le_one

theorem neighbor_eq_of_degree_le_two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u a b c : V)
    (hdeg : G.degree u ≤ 2) (ha : G.Adj u a) (hb : G.Adj u b)
    (hab : a ≠ b) (hc : G.Adj u c) : c = a ∨ c = b := by
  by_contra hn
  have hca : c ≠ a := fun h => hn (Or.inl h)
  have hcb : c ≠ b := fun h => hn (Or.inr h)
  have hsub : ({a, b, c} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx :
      x = a ∨ x = b ∨ x = c) with rfl | rfl | rfl
    · exact (G.mem_neighborFinset u x).mpr ha
    · exact (G.mem_neighborFinset u x).mpr hb
    · exact (G.mem_neighborFinset u x).mpr hc
  have hcard := Finset.card_mono hsub
  have hthree : ({a, b, c} : Finset V).card = 3 := by
    have ha_not : a ∉ ({b, c} : Finset V) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
        (show a ≠ b ∧ a ≠ c from ⟨hab, hca.symm⟩)
    have hb_not : b ∉ ({c} : Finset V) := by
      simpa only [Finset.mem_singleton] using hcb.symm
    simp only [Finset.card_insert_of_notMem ha_not,
      Finset.card_insert_of_notMem hb_not, Finset.card_singleton]
  rw [hthree, G.card_neighborFinset_eq_degree] at hcard
  omega
#print axioms Paper7TreeEndpointPath.neighbor_eq_of_degree_le_two

/-- Maximality is obtained from the finite set of possible path lengths,
without enumerating paths or assuming the existence of a covering path. -/
theorem exists_longest_path_from {V : Type} [Fintype V]
    (G : SimpleGraph V) (r : V) :
    ∃ (z : V) (p : G.Walk r z), p.IsPath ∧
      ∀ (z' : V) (q : G.Walk r z'), q.IsPath → q.length ≤ p.length := by
  let lengths : Set ℕ := {n | ∃ (z : V) (p : G.Walk r z), p.IsPath ∧ p.length = n}
  have hfinite : lengths.Finite :=
    (Set.finite_le_nat (Fintype.card V)).subset (by
      rintro n ⟨z, p, hp, rfl⟩
      exact hp.length_lt.le)
  obtain ⟨n, ⟨⟨z, p, hp, hlen⟩, hmax⟩⟩ :=
    hfinite.exists_maximal ⟨0, ⟨r, Walk.nil, by simp⟩⟩
  refine ⟨z, p, hp, ?_⟩
  intro z' q hq
  have hbound := hmax ⟨z', q, hq, rfl⟩
  by_cases hle : n ≤ q.length
  · have hle' := hbound hle
    omega
  · omega
#print axioms Paper7TreeEndpointPath.exists_longest_path_from

/-- A longest simple path from a vertex of degree at most one cannot have
an edge from its support to a new vertex when every degree is at most two. -/
theorem longest_path_from_endpoint_support_closed {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r z : V) (p : G.Walk r z)
    (hp : p.IsPath)
    (hmax : ∀ (z' : V) (q : G.Walk r z'), q.IsPath → q.length ≤ p.length)
    (hdeg : ∀ v, G.degree v ≤ 2) (hr : G.degree r ≤ 1) :
    ∀ u ∈ p.support, ∀ v, G.Adj u v → v ∈ p.support := by
  intro u hu v huv
  by_contra hv
  obtain ⟨i, hiu, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hu
  subst u
  by_cases hend : i = p.length
  · subst i
    rw [Walk.getVert_length] at huv
    have hbound := hmax v (p.concat huv) (hp.concat hv huv)
    simp only [Walk.length_concat] at hbound
    omega
  · have hilt : i < p.length := by omega
    by_cases hzero : i = 0
    · subst i
      have hfirst : G.Adj r (p.getVert 1) := by
        simpa only [Walk.getVert_zero] using p.adj_getVert_succ hilt
      have hrv : G.Adj r v := by simpa only [Walk.getVert_zero] using huv
      have heq := neighbors_eq_of_degree_le_one G r v (p.getVert 1) hr hrv hfirst
      exact hv (heq.symm ▸ p.getVert_mem_support 1)
    · have hiprev : i - 1 < p.length := by omega
      have hprev : G.Adj (p.getVert i) (p.getVert (i - 1)) := by
        have ha := (p.adj_getVert_succ hiprev).symm
        have heq : i - 1 + 1 = i := by omega
        simpa only [heq] using ha
      have hnext : G.Adj (p.getVert i) (p.getVert (i + 1)) :=
        p.adj_getVert_succ hilt
      have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
        intro heq
        have hij := hp.getVert_injOn
          (show i - 1 ≤ p.length by omega) (show i + 1 ≤ p.length by omega) heq
        omega
      have heq := neighbor_eq_of_degree_le_two G (p.getVert i)
        (p.getVert (i - 1)) (p.getVert (i + 1)) v (hdeg _) hprev hnext hne huv
      rcases heq with heq | heq
      · exact hv (heq.symm ▸ p.getVert_mem_support (i - 1))
      · exact hv (heq.symm ▸ p.getVert_mem_support (i + 1))
#print axioms Paper7TreeEndpointPath.longest_path_from_endpoint_support_closed

/-- Connectedness propagates membership along actual original-graph walks.
In particular the nil path handles a component with one vertex. -/
theorem connected_endpoint_spanning_path {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v ≤ 2) (r : V) (hr : G.degree r ≤ 1) :
    ∃ (z : V) (p : G.Walk r z), p.IsPath ∧ ∀ v, v ∈ p.support := by
  obtain ⟨z, p, hp, hmax⟩ := exists_longest_path_from G r
  have hclosed := longest_path_from_endpoint_support_closed G r z p hp hmax hdeg hr
  have hwalk : ∀ {u v : V}, G.Walk u v → u ∈ p.support → v ∈ p.support := by
    intro u v q
    induction q with
    | nil => exact id
    | @cons u v _z hadj _q ih =>
        intro hu
        exact ih (hclosed u hu v hadj)
  refine ⟨z, p, hp, ?_⟩
  intro v
  obtain ⟨q⟩ := hconn r v
  exact hwalk q p.start_mem_support
#print axioms Paper7TreeEndpointPath.connected_endpoint_spanning_path

/-- In an acyclic graph the actual simple path agrees with a shortest path. -/
theorem acyclic_path_length_eq_dist {V : Type} (G : SimpleGraph V)
    (hacyc : G.IsAcyclic) {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    p.length = G.dist u v := by
  obtain ⟨q, hq, hlen⟩ := p.reachable.exists_path_of_dist
  have heq : p = q := Subtype.mk.inj
    ((hacyc.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩)
  rw [heq]
  exact hlen
#print axioms Paper7TreeEndpointPath.acyclic_path_length_eq_dist

/-- There are exactly the consecutive-coordinate edges along a simple path
in an acyclic graph; this supplies both directions of the adjacency data. -/
theorem acyclic_path_getVert_adj_iff {V : Type} (G : SimpleGraph V)
    (hacyc : G.IsAcyclic) {r z : V} (p : G.Walk r z) (hp : p.IsPath)
    (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i + 1 = j ∨ j + 1 = i := by
  have hdi : G.dist r (p.getVert i) = i := by
    have h := acyclic_path_length_eq_dist G hacyc (p.take i) (hp.take i)
    simpa only [Walk.take_length, inf_eq_left.mpr hi] using h.symm
  have hdj : G.dist r (p.getVert j) = j := by
    have h := acyclic_path_length_eq_dist G hacyc (p.take j) (hp.take j)
    simpa only [Walk.take_length, inf_eq_left.mpr hj] using h.symm
  constructor
  · intro hadj
    have h := hacyc.dist_eq_dist_add_one_of_adj_of_reachable r hadj (p.take i).reachable
    rw [hdi, hdj] at h
    omega
  · rintro (hij | hji)
    · have hilt : i < p.length := by omega
      simpa only [hij] using p.adj_getVert_succ hilt
    · have hjlt : j < p.length := by omega
      simpa only [hji] using (p.adj_getVert_succ hjlt).symm
#print axioms Paper7TreeEndpointPath.acyclic_path_getVert_adj_iff

/-- Coverage and simplicity give an actual vertex bijection, including the
singleton case `Fin 1`; no positive edge-length premise is present. -/
theorem covering_path_getVert_bijective {V : Type} (G : SimpleGraph V)
    {r z : V} (p : G.Walk r z) (hp : p.IsPath) (hcover : ∀ v, v ∈ p.support) :
    Function.Bijective (fun i : Fin (p.length + 1) => p.getVert i.val) := by
  constructor
  · intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (show i.val ≤ p.length by omega)
      (show j.val ≤ p.length by omega) hij
  · intro v
    obtain ⟨i, hiv, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hcover v)
    exact ⟨⟨i, by omega⟩, hiv⟩
#print axioms Paper7TreeEndpointPath.covering_path_getVert_bijective

/-- The requested finite-tree helper: construct the covering simple path,
its full ordered vertex coordinates, its cardinality and exact adjacency. -/
theorem finite_tree_endpoint_path_data {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hacyc : G.IsAcyclic) (hdeg : ∀ v, G.degree v ≤ 2)
    (r : V) (hr : G.degree r ≤ 1) :
    ∃ (z : V) (p : G.Walk r z), p.IsPath ∧ (∀ v, v ∈ p.support) ∧
      p.length + 1 = Fintype.card V ∧
      Function.Bijective (fun i : Fin (p.length + 1) => p.getVert i.val) ∧
      ∀ i j : Fin (p.length + 1),
        G.Adj (p.getVert i.val) (p.getVert j.val) ↔
          i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  obtain ⟨z, p, hp, hcover⟩ := connected_endpoint_spanning_path G hconn hdeg r hr
  refine ⟨z, p, hp, hcover, ?_, covering_path_getVert_bijective G p hp hcover, ?_⟩
  · have hh := hp.isHamiltonian_of_mem hcover
    simpa only [Walk.length_support] using hh.length_support
  · intro i j
    exact acyclic_path_getVert_adj_iff G hacyc p hp i.val j.val
      (by omega) (by omega)
#print axioms Paper7TreeEndpointPath.finite_tree_endpoint_path_data

/-- The ordered data give a genuine graph isomorphism from a path graph,
with coordinate zero equal to the specified attachment vertex. -/
theorem finite_tree_endpoint_pathGraph_iso {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hacyc : G.IsAcyclic) (hdeg : ∀ v, G.degree v ≤ 2)
    (r : V) (hr : G.degree r ≤ 1) :
    ∃ (n : ℕ) (hn : 0 < n) (e : pathGraph n ≃g G),
      n = Fintype.card V ∧ e ⟨0, hn⟩ = r := by
  obtain ⟨z, p, _hp, _hcover, hcard, hbij, hadj⟩ :=
    finite_tree_endpoint_path_data G hconn hacyc hdeg r hr
  let coords : Fin (p.length + 1) ≃ V := Equiv.ofBijective _ hbij
  let e : pathGraph (p.length + 1) ≃g G :=
    { toEquiv := coords
      map_rel_iff' := by
        intro i j
        change G.Adj (p.getVert i.val) (p.getVert j.val) ↔
          (pathGraph (p.length + 1)).Adj i j
        rw [pathGraph_adj]
        exact hadj i j }
  refine ⟨p.length + 1, by omega, e, hcard, ?_⟩
  change p.getVert 0 = r
  exact p.getVert_zero
#print axioms Paper7TreeEndpointPath.finite_tree_endpoint_pathGraph_iso

end Paper7TreeEndpointPath
