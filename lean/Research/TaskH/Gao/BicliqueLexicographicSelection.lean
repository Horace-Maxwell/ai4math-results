import Mathlib

/-! Local casebi, primary 530–554. The two forbidden-pattern predicates below are
transparent interfaces for the still-owed upstream case1 and case3 conclusions.
They are not additional premises of Gao's original main theorem. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
variable {V : Type u}

def CasebiBiclique (G : SimpleGraph V) (x y : V)
    (A B : Set V) : Prop :=
  Disjoint A B ∧ (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∧
    x ∈ B ∧ y ∉ A ∪ B ∧ 2 ≤ B.ncard ∧ B.ncard ≤ A.ncard

def CasebiLexMax (G : SimpleGraph V) (x y : V)
    (A B : Set V) : Prop :=
  CasebiBiclique G x y A B ∧
    (∀ L M : Set V, CasebiBiclique G x y L M → M.ncard ≤ B.ncard) ∧
    (∀ L M : Set V, CasebiBiclique G x y L M →
      M.ncard = B.ncard → L.ncard ≤ A.ncard)

def CasebiNoRootTriangle (G : SimpleGraph V) (x y : V) : Prop :=
  ∀ a b : V, a ≠ y → b ≠ y →
    G.Adj x a → G.Adj a b → G.Adj b x → False

def CasebiNoTripleOnRootQuad (G : SimpleGraph V) (x y : V) : Prop :=
  ∀ a b c v : V, a ≠ c → x ≠ b → a ≠ y → b ≠ y → c ≠ y →
    G.Adj x a → G.Adj a b → G.Adj b c → G.Adj c x →
    v ≠ x → v ≠ a → v ≠ b → v ≠ c → v ≠ y →
    G.Adj v a → G.Adj v b → G.Adj v c → False

theorem casebi_exists_lexmax [Fintype V] (G : SimpleGraph V) (x y : V)
    (hseed : ∃ A B : Set V, CasebiBiclique G x y A B) :
    ∃ A B : Set V, CasebiLexMax G x y A B := by
  classical
  let S : Finset (Set V × Set V) :=
    Finset.univ.filter (fun p => CasebiBiclique G x y p.1 p.2)
  have hS : S.Nonempty := by
    obtain ⟨A, B, hAB⟩ := hseed
    exact ⟨(A, B), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAB⟩⟩
  obtain ⟨p, hp, hmaxB⟩ := Finset.exists_max_image S (fun q => q.2.ncard) hS
  let T : Finset (Set V × Set V) := S.filter (fun q => q.2.ncard = p.2.ncard)
  have hpT : p ∈ T := Finset.mem_filter.mpr ⟨hp, rfl⟩
  obtain ⟨q, hq, hmaxA⟩ :=
    Finset.exists_max_image T (fun r => r.1.ncard) ⟨p, hpT⟩
  have hqS : q ∈ S := (Finset.mem_filter.mp hq).1
  have hqB : q.2.ncard = p.2.ncard := (Finset.mem_filter.mp hq).2
  refine ⟨q.1, q.2, ⟨(Finset.mem_filter.mp hqS).2, ?_, ?_⟩⟩
  · intro L M hLM
    rw [hqB]
    exact hmaxB (L, M) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLM⟩)
  · intro L M hLM hcard
    apply hmaxA (L, M)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLM⟩, hcard.trans hqB⟩

theorem casebi_quad_seed (G : SimpleGraph V) (x y a b c : V)
    (hac : a ≠ c) (hxb : x ≠ b)
    (hxy : x ≠ y) (hay : a ≠ y) (hby : b ≠ y) (hcy : c ≠ y)
    (exa : G.Adj x a) (eab : G.Adj a b) (ebc : G.Adj b c)
    (ecx : G.Adj c x) :
    CasebiBiclique G x y ({a, c} : Set V) ({x, b} : Set V) := by
  classical
  have hcross : ∀ r ∈ ({a, c} : Set V), ∀ t ∈ ({x, b} : Set V), G.Adj r t := by
    intro r hr t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr ht
    rcases hr with rfl | rfl <;> rcases ht with rfl | rfl
    · exact exa.symm
    · exact eab
    · exact ecx
    · exact ebc.symm
  refine ⟨?_, hcross, by simp, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro z hzA hzB
    exact G.irrefl (hcross z hzA z hzB)
  · intro hy
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with (he | he) | (he | he)
    · exact hay he.symm
    · exact hcy he.symm
    · exact hxy he.symm
    · exact hby he.symm
  · exact le_of_eq (Set.ncard_pair hxb).symm
  · exact le_of_eq ((Set.ncard_pair hxb).trans (Set.ncard_pair hac).symm)

theorem casebi_lexmax_first_neighbor_cap [Fintype V] (G : SimpleGraph V)
    (x y : V) (A B : Set V) (hmax : CasebiLexMax G x y A B)
    (v : V) (hv : v ∉ (A ∪ B) ∪ {y}) :
    (G.neighborSet v ∩ A).ncard ≤ B.ncard := by
  classical
  rcases hmax with ⟨⟨hdis, hc, hx, hy, hB, _hBA⟩, hmaxB, _hmaxA⟩
  by_contra hn
  let L : Set V := G.neighborSet v ∩ A
  let M : Set V := insert v B
  have hvA : v ∉ A := fun h => hv (Or.inl (Or.inl h))
  have hvB : v ∉ B := fun h => hv (Or.inl (Or.inr h))
  have hvy : v ≠ y := by
    rintro rfl
    exact hv (Or.inr rfl)
  have hL : B.ncard + 1 ≤ L.ncard := by
    change ¬L.ncard ≤ B.ncard at hn
    omega
  have hM : M.ncard = B.ncard + 1 := Set.ncard_insert_of_notMem hvB
  have hd : Disjoint L M := by
    apply Set.disjoint_left.mpr
    intro z hzL hzM
    rcases Set.mem_insert_iff.mp hzM with he | hzB
    · subst z
      exact hvA hzL.2
    · exact Set.disjoint_left.mp hdis hzL.2 hzB
  have he : ∀ a ∈ L, ∀ b ∈ M, G.Adj a b := by
    intro a ha b hb
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact ha.1.symm
    · exact hc a ha.2 b hb
  have hyo : y ∉ L ∪ M := by
    rintro (hyL | hyM)
    · exact hy (Or.inl hyL.2)
    · rcases Set.mem_insert_iff.mp hyM with he | hyB
      · exact hvy he.symm
      · exact hy (Or.inr hyB)
  have hh := hmaxB L M ⟨hd, he, Set.mem_insert_of_mem v hx, hyo,
    by omega, by omega⟩
  omega

theorem casebi_lexmax_second_neighbor_cap [Fintype V] (G : SimpleGraph V)
    (x y : V) (A B : Set V) (hmax : CasebiLexMax G x y A B)
    (v : V) (hv : v ∉ (A ∪ B) ∪ {y}) :
    (G.neighborSet v ∩ B).ncard < B.ncard := by
  classical
  rcases hmax with ⟨⟨hdis, hc, hx, hy, hB, hBA⟩, _hmaxB, hmaxA⟩
  by_contra hn
  have hcard : B.ncard ≤ (G.neighborSet v ∩ B).ncard := by omega
  have hfull : G.neighborSet v ∩ B = B :=
    Set.eq_of_subset_of_ncard_le Set.inter_subset_right hcard (Set.toFinite B)
  have hvA : v ∉ A := fun h => hv (Or.inl (Or.inl h))
  have hvB : v ∉ B := fun h => hv (Or.inl (Or.inr h))
  have hvy : v ≠ y := by
    rintro rfl
    exact hv (Or.inr rfl)
  have hnew : CasebiBiclique G x y (insert v A) B := by
    refine ⟨?_, ?_, hx, ?_, hB, ?_⟩
    · apply Set.disjoint_left.mpr
      intro z hz hzB
      rcases Set.mem_insert_iff.mp hz with rfl | hzA
      · exact hvB hzB
      · exact Set.disjoint_left.mp hdis hzA hzB
    · intro a ha b hb
      rcases Set.mem_insert_iff.mp ha with he | haA
      · have hbfull : b ∈ G.neighborSet v ∩ B :=
          Eq.mpr (congrArg (fun S : Set V => b ∈ S) hfull) hb
        exact Eq.mpr (congrArg (fun z : V => G.Adj z b) he) hbfull.1
      · exact hc a haA b hb
    · rintro (hyA | hyB)
      · rcases Set.mem_insert_iff.mp hyA with he | hyA
        · exact hvy he.symm
        · exact hy (Or.inl hyA)
      · exact hy (Or.inr hyB)
    · exact hBA.trans (Set.ncard_le_ncard_insert v A)
  have hh := hmaxA (insert v A) B hnew rfl
  rw [Set.ncard_insert_of_notMem hvA] at hh
  omega

theorem casebi_mixed_first_card (G : SimpleGraph V)
    (x y : V) (A B : Set V) (hQ : CasebiBiclique G x y A B)
    (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (v : V) (hv : v ∉ (A ∪ B) ∪ {y})
    (hA : ∃ a ∈ A, G.Adj v a) (hB : ∃ b ∈ B, G.Adj v b) :
    (G.neighborSet v ∩ A).ncard = 1 := by
  classical
  rcases hQ with ⟨hdis, hc, hx, hy, _hBcard, _hBA⟩
  obtain ⟨a, ha, eva⟩ := hA
  obtain ⟨b, hb, evb⟩ := hB
  have hAy : ∀ z ∈ A, z ≠ y := by
    intro z hz he
    subst z
    exact hy (Or.inl hz)
  have hBy : ∀ z ∈ B, z ≠ y := by
    intro z hz he
    subst z
    exact hy (Or.inr hz)
  have hvA : v ∉ A := fun h => hv (Or.inl (Or.inl h))
  have hvB : v ∉ B := fun h => hv (Or.inl (Or.inr h))
  have hvx : v ≠ x := by
    rintro rfl
    exact hvB hx
  have hvy : v ≠ y := by
    rintro rfl
    exact hv (Or.inr rfl)
  have hbx : b ≠ x := by
    intro he
    subst b
    exact htri a v (hAy a ha) hvy (hc a ha x hx).symm eva.symm evb
  have hu : ∀ c ∈ G.neighborSet v ∩ A, c = a := by
    intro c hcN
    by_contra hca
    apply hquad a b c v (fun he => hca he.symm) hbx.symm (hAy a ha) (hBy b hb)
      (hAy c hcN.2) (hc a ha x hx).symm (hc a ha b hb)
      (hc c hcN.2 b hb).symm (hc c hcN.2 x hx) hvx
    · rintro rfl
      exact hvA ha
    · rintro rfl
      exact hvB hb
    · rintro rfl
      exact hvA hcN.2
    · exact hvy
    · exact eva
    · exact evb
    · exact hcN.1
  have heq : G.neighborSet v ∩ A = {a} := by
    ext c
    constructor
    · exact fun hcN => hu c hcN
    · intro hca
      have hca' : c = a := hca
      subst c
      exact ⟨eva, ha⟩
  rw [heq, Set.ncard_singleton]

theorem casebi_parts_independent [Fintype V] (G : SimpleGraph V)
    (x y : V) (A B : Set V) (hQ : CasebiBiclique G x y A B)
    (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y) :
    (∀ a ∈ A, ∀ c ∈ A, ¬G.Adj a c) ∧
      (∀ b ∈ B, ∀ d ∈ B, ¬G.Adj b d) := by
  classical
  rcases hQ with ⟨hdis, hc, hx, hy, hB, hBA⟩
  have hAy : ∀ z ∈ A, z ≠ y := by
    intro z hz he
    subst z
    exact hy (Or.inl hz)
  have hBy : ∀ z ∈ B, z ≠ y := by
    intro z hz he
    subst z
    exact hy (Or.inr hz)
  have htwo : 1 < A.ncard := by omega
  obtain ⟨a, ha, c, hcA, hac⟩ := (Set.one_lt_ncard (Set.toFinite A)).mp htwo
  constructor
  · intro r hr t ht ert
    exact htri r t (hAy r hr) (hAy t ht) (hc r hr x hx).symm
      ert (hc t ht x hx)
  · intro b hb d hd ebd
    have hbx : b ≠ x := by
      intro he
      subst b
      exact htri a d (hAy a ha) (hBy d hd) (hc a ha x hx).symm
        (hc a ha d hd) ebd.symm
    have hdx : d ≠ x := by
      intro he
      subst d
      exact htri a b (hAy a ha) (hBy b hb) (hc a ha x hx).symm
        (hc a ha b hb) ebd
    apply hquad a b c d hac hbx.symm (hAy a ha) (hBy b hb) (hAy c hcA)
      (hc a ha x hx).symm (hc a ha b hb) (hc c hcA b hb).symm
      (hc c hcA x hx) hdx
    · intro he
      subst d
      exact Set.disjoint_left.mp hdis ha hd
    · exact ebd.ne.symm
    · intro he
      subst d
      exact Set.disjoint_left.mp hdis hcA hd
    · exact hBy d hd
    · exact (hc a ha d hd).symm
    · exact ebd.symm
    · exact (hc c hcA d hd).symm

theorem casebi_induced_adjacency [Fintype V] (G : SimpleGraph V)
    (x y : V) (A B : Set V) (hQ : CasebiBiclique G x y A B)
    (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (r t : V) (hr : r ∈ A ∪ B) (ht : t ∈ A ∪ B) :
    G.Adj r t ↔ (r ∈ A ∧ t ∈ B) ∨ (r ∈ B ∧ t ∈ A) := by
  obtain ⟨hAA, hBB⟩ := casebi_parts_independent G x y A B hQ htri hquad
  constructor
  · intro ert
    rcases hr with hr | hr <;> rcases ht with ht | ht
    · exact False.elim (hAA r hr t ht ert)
    · exact Or.inl ⟨hr, ht⟩
    · exact Or.inr ⟨hr, ht⟩
    · exact False.elim (hBB r hr t ht ert)
  · rintro (⟨hrA, htB⟩ | ⟨hrB, htA⟩)
    · exact hQ.2.1 r hrA t htB
    · exact (hQ.2.1 t htA r hrB).symm

theorem casebi_lexmax_total_neighbor_cap [Fintype V] (G : SimpleGraph V)
    (x y : V) (A B : Set V) (hmax : CasebiLexMax G x y A B)
    (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (v : V) (hv : v ∉ (A ∪ B) ∪ {y}) :
    (G.neighborSet v ∩ (A ∪ B)).ncard ≤ B.ncard := by
  classical
  have hcapA := casebi_lexmax_first_neighbor_cap G x y A B hmax v hv
  have hcapB := casebi_lexmax_second_neighbor_cap G x y A B hmax v hv
  have hd : Disjoint (G.neighborSet v ∩ A) (G.neighborSet v ∩ B) := by
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    exact Set.disjoint_left.mp hmax.1.1 hzA.2 hzB.2
  have heq : G.neighborSet v ∩ (A ∪ B) =
      (G.neighborSet v ∩ A) ∪ (G.neighborSet v ∩ B) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  rw [heq, Set.ncard_union_eq hd]
  by_cases hA : G.neighborSet v ∩ A = ∅
  · rw [hA, Set.ncard_empty]
    omega
  · by_cases hB : G.neighborSet v ∩ B = ∅
    · rw [hB, Set.ncard_empty]
      omega
    · obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hA
      obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.mpr hB
      have hm := casebi_mixed_first_card G x y A B hmax.1 htri hquad v hv
        ⟨a, ha.2, ha.1⟩ ⟨b, hb.2, hb.1⟩
      omega

theorem casebi_from_actual_root_quad [Fintype V] (G : SimpleGraph V)
    (x y a b c : V) (hac : a ≠ c) (hxb : x ≠ b)
    (hxy : x ≠ y) (hay : a ≠ y) (hby : b ≠ y) (hcy : c ≠ y)
    (exa : G.Adj x a) (eab : G.Adj a b) (ebc : G.Adj b c)
    (ecx : G.Adj c x)
    (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y) :
    ∃ (s : ℕ) (A B : Set V), 1 ≤ s ∧ CasebiLexMax G x y A B ∧
      B.ncard = s + 1 ∧
      (∀ r ∈ A ∪ B, ∀ t ∈ A ∪ B,
        G.Adj r t ↔ (r ∈ A ∧ t ∈ B) ∨ (r ∈ B ∧ t ∈ A)) ∧
      (∀ v ∉ (A ∪ B) ∪ {y},
        (G.neighborSet v ∩ (A ∪ B)).ncard ≤ s + 1 ∧
        (G.neighborSet v ∩ A).ncard ≤ s + 1 ∧
        (G.neighborSet v ∩ B).ncard ≤ s ∧
        ((∃ r ∈ A, G.Adj v r) → (∃ t ∈ B, G.Adj v t) →
          (G.neighborSet v ∩ A).ncard = 1)) := by
  classical
  obtain ⟨A, B, hmax⟩ := casebi_exists_lexmax G x y
    ⟨{a, c}, {x, b}, casebi_quad_seed G x y a b c hac hxb hxy hay hby hcy
      exa eab ebc ecx⟩
  let s := B.ncard - 1
  have hB : 2 ≤ B.ncard := hmax.1.2.2.2.2.1
  have hs : 1 ≤ s := by omega
  have hBs : B.ncard = s + 1 := by omega
  refine ⟨s, A, B, hs, hmax, hBs, ?_, ?_⟩
  · intro r hr t ht
    exact casebi_induced_adjacency G x y A B hmax.1 htri hquad r t hr ht
  · intro v hv
    have ht := casebi_lexmax_total_neighbor_cap G x y A B hmax htri hquad v hv
    have hA := casebi_lexmax_first_neighbor_cap G x y A B hmax v hv
    have hBv := casebi_lexmax_second_neighbor_cap G x y A B hmax v hv
    refine ⟨by omega, by omega, by omega, ?_⟩
    exact casebi_mixed_first_card G x y A B hmax.1 htri hquad v hv

#print axioms CasebiBiclique
#print axioms CasebiLexMax
#print axioms CasebiNoRootTriangle
#print axioms CasebiNoTripleOnRootQuad
#print axioms casebi_exists_lexmax
#print axioms casebi_quad_seed
#print axioms casebi_lexmax_first_neighbor_cap
#print axioms casebi_lexmax_second_neighbor_cap
#print axioms casebi_mixed_first_card
#print axioms casebi_parts_independent
#print axioms casebi_induced_adjacency
#print axioms casebi_lexmax_total_neighbor_cap
#print axioms casebi_from_actual_root_quad
end TaskH.Gao
