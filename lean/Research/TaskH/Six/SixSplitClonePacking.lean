import Research.TaskH.Six.SixRainbowHexagonCollision
import Research.TaskH.Six.SixOpenNeighborhoodPacking

/-!
Actual same-color two-leaf clones in a deleted coloring. The common-neighbor
contradiction uses two explicit real hexagons, including the separate case
where the shared neighbor is the star center and the hexagon contains v.
The fixed coloring and clone membership must be derived in the split branch.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

theorem same_color_two_leaf_common_neighbor_unique
    (hr : RainbowSixCycles G) (v a p q : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (hva : G.Adj v a) (hvp : G.Adj v p) (hvq : G.Adj v q)
    (hap : G.Adj a p) (haq : G.Adj a q) (hpq : p ≠ q)
    (Z : Finset V)
    (hout : ∀ z ∈ Z, z ≠ v ∧ ¬ G.Adj v z)
    (hleaves : ∀ z ∈ Z, G.Adj z p ∧ G.Adj z q)
    (hcolor : ∀ z (hz : z ∈ Z), ∀ z' (hz' : z' ∈ Z),
      c ⟨z, (hout z hz).1⟩ = c ⟨z', (hout z' hz').1⟩) :
    ∀ z ∈ Z, ∀ z' ∈ Z, ∀ t : V, t ≠ p → t ≠ q →
      G.Adj z t → G.Adj z' t → z = z' := by
  intro z hz z' hz' t htp htq hzt hz't
  by_contra hzz'
  have hzv := (hout z hz).1
  have hz'v := (hout z' hz').1
  have hz_not := (hout z hz).2
  have hz'_not := (hout z' hz').2
  have hzp := (hleaves z hz).1
  have hzq := (hleaves z hz).2
  have hz'p := (hleaves z' hz').1
  have hz'q := (hleaves z' hz').2
  have hza : z ≠ a := by intro he; exact hz_not (by simpa only [he] using hva)
  have hz'a : z' ≠ a := by intro he; exact hz'_not (by simpa only [he] using hva)
  have htv : t ≠ v := by intro he; exact hz_not (he ▸ hzt.symm)
  have hpv := hvp.ne.symm
  have hqv := hvq.ne.symm
  have hav := hva.ne.symm
  have hpa := hap.ne.symm
  have hqa := haq.ne.symm
  have hzp_ne := hzp.ne
  have hzq_ne := hzq.ne
  have hz'p_ne := hz'p.ne
  have hz'q_ne := hz'q.ne
  have hzt_ne := hzt.ne
  have hz't_ne := hz't.ne
  by_cases hta : t = a
  · let f : Fin 6 → V := ![z, p, v, q, z', a]
    have hlist : ([z, p, v, q, z', a] : List V).Nodup := by
      simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, not_or,
        List.not_mem_nil, not_false_eq_true, and_true]
      exact ⟨⟨hzp_ne, hzv, hzq_ne, hzz', hza⟩,
        ⟨hpv, hpq, hz'p_ne.symm, hpa⟩, ⟨hvq.ne, hz'v.symm, hva.ne⟩,
        ⟨hz'q_ne.symm, hqa⟩, hz'a⟩
    have hfi : Function.Injective f := by
      have he : f = ([z, p, v, q, z', a] : List V).get := by
        funext k
        fin_cases k <;> rfl
      rw [he]
      exact List.nodup_iff_injective_get.mp hlist
    have hf : IsHexagon G f :=
      ⟨hfi, hzp, hvp.symm, hvq, hz'q.symm, by change G.Adj z' a; simpa only [hta] using hz't,
        by change G.Adj a z; simpa only [hta] using hzt.symm⟩
    exact rainbow_hexagon_same_color_impossible hr v c f hf z z' hzv hz'v hzz'
      ⟨0, rfl⟩ ⟨4, rfl⟩ (hcolor z hz z' hz')
  · let f : Fin 6 → V := ![z, p, a, q, z', t]
    have hlist : ([z, p, a, q, z', t] : List V).Nodup := by
      simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, not_or,
        List.not_mem_nil, not_false_eq_true, and_true]
      exact ⟨⟨hzp_ne, hza, hzq_ne, hzz', hzt_ne⟩,
        ⟨hpa, hpq, hz'p_ne.symm, htp.symm⟩, ⟨haq.ne, hz'a.symm, (Ne.symm hta)⟩,
        ⟨hz'q_ne.symm, htq.symm⟩, hz't_ne⟩
    have hfi : Function.Injective f := by
      have he : f = ([z, p, a, q, z', t] : List V).get := by
        funext k
        fin_cases k <;> rfl
      rw [he]
      exact List.nodup_iff_injective_get.mp hlist
    have hf : IsHexagon G f :=
      ⟨hfi, hzp, hap.symm, haq, hz'q.symm, hz't, hzt.symm⟩
    exact rainbow_hexagon_same_color_impossible hr v c f hf z z' hzv hz'v hzz'
      ⟨0, rfl⟩ ⟨4, rfl⟩ (hcolor z hz z' hz')

theorem same_color_two_leaf_clone_card_le_three [Fintype V] [DecidableRel G.Adj]
    (hr : RainbowSixCycles G) (v a p q : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (hva : G.Adj v a) (hvp : G.Adj v p) (hvq : G.Adj v q)
    (hap : G.Adj a p) (haq : G.Adj a q) (hpq : p ≠ q)
    (Z : Finset V)
    (hout : ∀ z ∈ Z, z ≠ v ∧ ¬ G.Adj v z)
    (hleaves : ∀ z ∈ Z, G.Adj z p ∧ G.Adj z q)
    (hcolor : ∀ z (hz : z ∈ Z), ∀ z' (hz' : z' ∈ Z),
      c ⟨z, (hout z hz).1⟩ = c ⟨z', (hout z' hz').1⟩)
    (hdegree : ∀ z ∈ Z, 10 ≤ G.degree z)
    (hn : Fintype.card V ≤ 36) : Z.card ≤ 3 := by
  classical
  let S : Finset V := (Z ∪ {p, q})ᶜ
  have hind : ∀ z ∈ Z, ∀ z' ∈ Z, ¬ G.Adj z z' := by
    intro z hz z' hz' hzz'
    have ha : (G.induce {x | x ≠ v}).Adj
        ⟨z, (hout z hz).1⟩ ⟨z', (hout z' hz').1⟩ := hzz'
    exact (c.valid ha) (hcolor z hz z' hz')
  have hrow : ∀ z ∈ Z, 8 ≤ (packingNeighborsIn G S z).card := by
    intro z hz
    have he : packingNeighborsIn G Sᶜ z = packingNeighborsIn G {p, q} z := by
      ext t
      simp only [packingNeighborsIn, Finset.mem_filter, S, compl_compl,
        Finset.mem_union]
      constructor
      · rintro ⟨ht, hzt⟩
        exact ⟨ht.resolve_left (fun htZ => hind z hz t htZ hzt), hzt⟩
      · rintro ⟨ht, hzt⟩
        exact ⟨Or.inr ht, hzt⟩
    have hi : (packingNeighborsIn G Sᶜ z).card ≤ 2 := by
      rw [he]
      exact (Finset.card_le_card (packingNeighborsIn_subset (G := G) {p, q} z)).trans
        (Finset.card_pair hpq).le
    have hh := packingNeighborsIn_compl_lower Sᶜ z 10 2 (hdegree z hz) hi
    simpa only [compl_compl] using hh
  have hcommon : ∀ t ∈ S, ∀ z ∈ Z, ∀ z' ∈ Z,
      G.Adj z t → G.Adj z' t → z = z' := by
    intro t ht z hz z' hz' hzt hz't
    have hnS : t ∉ Z ∪ {p, q} := Finset.mem_compl.mp ht
    have htp : t ≠ p := by intro he; apply hnS; simp [he]
    have htq : t ≠ q := by intro he; apply hnS; simp [he]
    exact same_color_two_leaf_common_neighbor_unique hr v a p q c hva hvp hvq
      hap haq hpq Z hout hleaves hcolor z hz z' hz' t htp htq hzt hz't
  have hpack := actual_open_neighborhood_uniform_packing Z S 8 hrow hcommon
  have hdisj : Disjoint Z {p, q} := by
    apply Finset.disjoint_left.mpr
    intro z hz hzpair
    rcases (show z = p ∨ z = q by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hzpair) with he | he
    · exact (hout z hz).2 (by simpa only [he] using hvp)
    · exact (hout z hz).2 (by simpa only [he] using hvq)
  have hcard : (Z ∪ {p, q}).card = Z.card + 2 := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair hpq]
  have hc := Finset.card_add_card_compl (Z ∪ {p, q})
  rw [hcard] at hc
  change Z.card + 2 + S.card = Fintype.card V at hc
  omega

end TaskH.Six

#print axioms TaskH.Six.same_color_two_leaf_common_neighbor_unique
#print axioms TaskH.Six.same_color_two_leaf_clone_card_le_three
