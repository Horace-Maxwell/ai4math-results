import Research.TaskH.Gao.CaseThreeCoreChoice
import Research.TaskH.Gao.CliquePrefixFamily

/-! Original Case3 facts (a),(b): actual simple paths with exact consecutive lengths. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem case3_core_insert_clique (G : SimpleGraph V) (x y p q : V) (K : Set V)
    (hK : G.IsClique K) (hsub : K ⊆ case3CoreDomain G x y p q) :
    G.IsClique (insert q K) := by
  apply SimpleGraph.isClique_insert.mpr
  exact ⟨hK, fun z hz _hne => (hsub hz).2.2.2.2.2⟩

theorem case3_core_path_to_member [Finite V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (hK : G.IsClique K)
    (hsub : K ⊆ case3CoreDomain G x y p q) (hcard : 2 ≤ K.ncard)
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q) (u : V) (hu : u ∈ K)
    (j : ℕ) (hj : 2 ≤ j) (hjt : j ≤ K.ncard + 2) :
    ∃ r : G.Walk x u, r.IsPath ∧ r.length = j ∧
      ∀ z ∈ r.support, z ∈ insert x (insert p (insert q K)) := by
  classical
  have hux : u ≠ x := (hsub hu).1
  have epu : G.Adj p u := (hsub hu).2.2.2.2.1
  by_cases hj2 : j = 2
  · let r : G.Walk x u := Walk.cons exp epu.toWalk
    have hxp : x ∉ epu.toWalk.support := by
      rw [SimpleGraph.Adj.support_toWalk]
      intro hz
      have hh : x = p ∨ x = u := by simpa using hz
      exact hh.elim exp.ne hux.symm
    refine ⟨r, epu.isPath_toWalk.cons hxp, ?_, ?_⟩
    · change (Walk.cons exp epu.toWalk).length = j
      rw [Walk.length_cons, epu.length_toWalk]
      omega
    · intro z hz
      change z ∈ x :: epu.toWalk.support at hz
      rcases List.mem_cons.mp hz with he | hz
      · exact Set.mem_insert_iff.mpr (Or.inl he)
      · rw [SimpleGraph.Adj.support_toWalk] at hz
        have hh : z = p ∨ z = u := by simpa using hz
        rcases hh with he | he
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr (Or.inr (Eq.mpr (congrArg (fun z : V => z ∈ K) he) hu)))
  · have htwo : 1 < K.ncard := by omega
    obtain ⟨c, d, hc, hd, hcd⟩ := (Set.one_lt_ncard_iff (Set.toFinite K)).mp htwo
    have hex : ∃ v ∈ K, v ≠ u := by
      by_cases hcu : c = u
      · exact ⟨d, hd, fun hdu => hcd (hcu.trans hdu.symm)⟩
      · exact ⟨c, hc, hcu⟩
    obtain ⟨v, hv, hvu⟩ := hex
    let L : Set V := insert q K
    have hqK : q ∉ K := fun hq => (hsub hq).2.2.2.1 rfl
    have hLc : L.ncard = K.ncard + 1 := Set.ncard_insert_of_notMem hqK
    have hLcl : G.IsClique L := case3_core_insert_clique G x y p q K hK hsub
    have hpL : p ∉ L := by
      rintro (hpq' | hpK)
      · exact hpq hpq'
      · exact (hsub hpK).2.2.1 rfl
    have hxL : x ∉ L := by
      rintro (hxq | hxK)
      · exact exq.ne hxq
      · exact (hsub hxK).1 rfl
    obtain ⟨r, hr, hlen, hsupp⟩ := clique_path_length L hLcl (by omega)
      v u (Or.inr hv) (Or.inr hu) hvu (j - 2) (by omega) (by omega)
    have epv : G.Adj p v := (hsub hv).2.2.2.2.1
    have hpR : p ∉ r.support := fun hz => hpL (hsupp p hz)
    have hxR : x ∉ (Walk.cons epv r).support := by
      rw [Walk.support_cons]
      intro hz
      rcases List.mem_cons.mp hz with he | hz
      · exact exp.ne he
      · exact hxL (hsupp x hz)
    refine ⟨Walk.cons exp (Walk.cons epv r), (hr.cons hpR).cons hxR, ?_, ?_⟩
    · rw [Walk.length_cons, Walk.length_cons, hlen]
      omega
    · intro z hz
      rw [Walk.support_cons] at hz
      rcases List.mem_cons.mp hz with he | hz
      · exact Or.inl he
      · rw [Walk.support_cons] at hz
        rcases List.mem_cons.mp hz with he | hz
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr (hsupp z hz))

theorem case3_core_path_to_neighbor [Finite V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (hK : G.IsClique K)
    (hsub : K ⊆ case3CoreDomain G x y p q) (hcard : 2 ≤ K.ncard)
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q)
    (j : ℕ) (hj : 3 ≤ j) (hjt : j ≤ K.ncard + 2) :
    ∃ r : G.Walk x p, r.IsPath ∧ r.length = j ∧
      ∀ z ∈ r.support, z ∈ insert x (insert p (insert q K)) := by
  classical
  obtain ⟨v, hv⟩ := (Set.ncard_pos (Set.toFinite K)).mp (by omega : 0 < K.ncard)
  let L : Set V := insert p K
  have hpK : p ∉ K := fun hp => (hsub hp).2.2.1 rfl
  have hLc : L.ncard = K.ncard + 1 := Set.ncard_insert_of_notMem hpK
  have hLcl : G.IsClique L := by
    apply SimpleGraph.isClique_insert.mpr
    exact ⟨hK, fun z hz _hne => (hsub hz).2.2.2.2.1⟩
  have hqL : q ∉ L := by
    rintro (hqp | hqK)
    · exact hpq hqp.symm
    · exact (hsub hqK).2.2.2.1 rfl
  have hxL : x ∉ L := by
    rintro (hxp | hxK)
    · exact exp.ne hxp
    · exact (hsub hxK).1 rfl
  have hvp : v ≠ p := (hsub hv).2.2.1
  obtain ⟨r, hr, hlen, hsupp⟩ := clique_path_length L hLcl (by omega)
    v p (Or.inr hv) (Or.inl rfl) hvp (j - 2) (by omega) (by omega)
  have eqv : G.Adj q v := (hsub hv).2.2.2.2.2
  have hqR : q ∉ r.support := fun hz => hqL (hsupp q hz)
  have hxR : x ∉ (Walk.cons eqv r).support := by
    rw [Walk.support_cons]
    intro hz
    rcases List.mem_cons.mp hz with he | hz
    · exact exq.ne he
    · exact hxL (hsupp x hz)
  refine ⟨Walk.cons exq (Walk.cons eqv r), (hr.cons hqR).cons hxR, ?_, ?_⟩
  · rw [Walk.length_cons, Walk.length_cons, hlen]
    omega
  · intro z hz
    rw [Walk.support_cons] at hz
    rcases List.mem_cons.mp hz with he | hz
    · exact Or.inl he
    · rw [Walk.support_cons] at hz
      rcases List.mem_cons.mp hz with he | hz
      · exact Or.inr (Or.inr (Or.inl he))
      · rcases hsupp z hz with he | hzK
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr (Or.inr hzK))

theorem case3_core_member_family [Finite V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (hK : G.IsClique K)
    (hsub : K ⊆ case3CoreDomain G x y p q) (hcard : 2 ≤ K.ncard)
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q) (u : V) (hu : u ∈ K) :
    ∃ r : Fin (K.ncard + 1) → G.Walk x u,
      AdmissiblePathFamily G x u (K.ncard + 1) 2 1 r ∧
        ∀ i z, z ∈ (r i).support → z ∈ insert x (insert p (insert q K)) := by
  classical
  have hex : ∀ i : Fin (K.ncard + 1), ∃ r : G.Walk x u,
      r.IsPath ∧ r.length = i.val + 2 ∧
        ∀ z ∈ r.support, z ∈ insert x (insert p (insert q K)) := by
    intro i
    have hi := i.isLt
    exact case3_core_path_to_member G x y p q K hK hsub hcard exp exq hpq u hu
      (i.val + 2) (by omega) (by omega)
  choose r hpath hlength hsupp using hex
  refine ⟨r, ⟨by omega, Or.inl rfl, ?_⟩, hsupp⟩
  intro i
  refine ⟨hpath i, ?_⟩
  have hh := hlength i
  omega

theorem case3_core_neighbor_family [Finite V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (hK : G.IsClique K)
    (hsub : K ⊆ case3CoreDomain G x y p q) (hcard : 2 ≤ K.ncard)
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q) :
    ∃ r : Fin K.ncard → G.Walk x p,
      AdmissiblePathFamily G x p K.ncard 3 1 r ∧
        ∀ i z, z ∈ (r i).support → z ∈ insert x (insert p (insert q K)) := by
  classical
  have hex : ∀ i : Fin K.ncard, ∃ r : G.Walk x p,
      r.IsPath ∧ r.length = i.val + 3 ∧
        ∀ z ∈ r.support, z ∈ insert x (insert p (insert q K)) := by
    intro i
    have hi := i.isLt
    exact case3_core_path_to_neighbor G x y p q K hK hsub hcard exp exq hpq
      (i.val + 3) (by omega) (by omega)
  choose r hpath hlength hsupp using hex
  refine ⟨r, ⟨by omega, Or.inl rfl, ?_⟩, hsupp⟩
  intro i
  refine ⟨hpath i, ?_⟩
  have hh := hlength i
  omega

theorem case3_core_other_neighbor_family [Finite V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (hK : G.IsClique K)
    (hsub : K ⊆ case3CoreDomain G x y p q) (hcard : 2 ≤ K.ncard)
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q) :
    ∃ r : Fin K.ncard → G.Walk x q,
      AdmissiblePathFamily G x q K.ncard 3 1 r ∧
        ∀ i z, z ∈ (r i).support → z ∈ insert x (insert p (insert q K)) := by
  have hswap : K ⊆ case3CoreDomain G x y q p := by
    rw [case3CoreDomain_swap G x y p q]
    exact hsub
  obtain ⟨r, hr, hsupp⟩ := case3_core_neighbor_family G x y q p K hK hswap hcard exq exp hpq.symm
  refine ⟨r, hr, ?_⟩
  intro i z hz
  rcases hsupp i z hz with he | he | he | hzK
  · exact Or.inl he
  · exact Or.inr (Or.inr (Or.inl he))
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (Or.inr hzK))

#print axioms case3_core_insert_clique
#print axioms case3_core_path_to_member
#print axioms case3_core_path_to_neighbor
#print axioms case3_core_member_family
#print axioms case3_core_neighbor_family
#print axioms case3_core_other_neighbor_family
end TaskH.Gao
