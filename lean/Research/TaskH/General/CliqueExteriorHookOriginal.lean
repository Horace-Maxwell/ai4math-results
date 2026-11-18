import Research.TaskH.General.EqualityRainbowOriginal
import Research.TaskH.Gao.CliquePaths

/-! A k-clique and two actual exterior points give a different deleted-root
coloring internally. No color of the original singleton coloring is reused. -/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_original_k_clique_two_exterior_hooks (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (Q : Finset V) (hQ : G.IsClique (Q : Set V)) (hcard : Q.card = k)
    {z w a b : V} (hzQ : z ∉ Q) (hwQ : w ∉ Q) (hzw : z ≠ w)
    (ha : a ∈ Q) (hb : b ∈ Q) (hab : a ≠ b)
    (hza : G.Adj z a) (hzb : G.Adj z b) : False := by
  classical
  obtain ⟨c⟩ := _root_.TaskH.critical_colorable_deletedVertex hcrit w
  let f : Q → Fin k := fun u => c ⟨u.val, fun he => hwQ (he ▸ u.property)⟩
  have hf : Function.Injective f := by
    intro u u' he
    by_contra hne
    have hAdj : G.Adj u.val u'.val :=
      hQ u.property u'.property (fun hv => hne (Subtype.ext hv))
    have hAdj' : (G.induce {x | x ≠ w}).Adj
        ⟨u.val, fun h => hwQ (h ▸ u.property)⟩
        ⟨u'.val, fun h => hwQ (h ▸ u'.property)⟩ := hAdj
    exact c.valid hAdj' he
  have hcards : Fintype.card Q = Fintype.card (Fin k) := by
    rw [Fintype.card_coe, hcard, Fintype.card_fin]
  have hsurj := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcards⟩).2
  obtain ⟨u, huColor⟩ := hsurj (c ⟨z, hzw⟩)
  have hd : ∃ d ∈ Q, d ≠ a ∧ d ≠ b ∧ d ≠ u.val := by
    by_contra! hn
    have hsub : Q ⊆ ({a, b, u.val} : Finset V) := by
      intro d hdQ
      by_cases hda : d = a
      · simp [hda]
      by_cases hdb : d = b
      · simp [hdb]
      have hdu : d = u.val := hn d hdQ hda hdb
      simp [hdu]
    have hle := Finset.card_le_card hsub
    have hthree : ({a, b, u.val} : Finset V).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨d, hdQ, hda, hdb, hdu⟩ := hd
  let K := Q.erase d
  have hKcard : K.card = k - 1 := by
    exact (Finset.card_erase_of_mem hdQ).trans (congrArg (fun n => n - 1) hcard)
  have haK : a ∈ K := Finset.mem_erase.mpr ⟨hda.symm, ha⟩
  have hbK : b ∈ K := Finset.mem_erase.mpr ⟨hdb.symm, hb⟩
  have huK : u.val ∈ K := Finset.mem_erase.mpr ⟨hdu.symm, u.property⟩
  have hK : G.IsClique (K : Set V) := by
    intro p hp q hq hpq
    exact hQ (Finset.mem_of_mem_erase hp) (Finset.mem_of_mem_erase hq) hpq
  obtain ⟨L, hL, hLen, hSupp⟩ := _root_.TaskH.Gao.finset_clique_path_exact
    (k - 2) K a b hK haK hbK hab (by omega) (by omega)
  have hfull : L.support.toFinset = K := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      exact hSupp x (List.mem_toFinset.mp hx)
    · rw [List.toFinset_card_of_nodup hL.support_nodup, Walk.length_support, hLen, hKcard]
      omega
  have huL : u.val ∈ L.support := by
    rw [← List.mem_toFinset, hfull]
    exact huK
  have hzL : z ∉ L.support := by
    intro hh
    exact hzQ (Finset.mem_of_mem_erase (hSupp z hh))
  let p := Walk.cons hza L
  have hp : p.IsPath := hL.cons hzL
  have hzTail : z ∉ p.support.tail := by
    have hn : (z :: p.support.tail).Nodup := by
      rw [Walk.cons_tail_support p]
      exact hp.support_nodup
    exact (List.nodup_cons.mp hn).1
  have hDisj : p.support.tail.Disjoint hzb.symm.toWalk.support.tail := by
    rw [List.disjoint_left]
    intro x hx hx'
    have he : x = z := by
      simpa only [SimpleGraph.Adj.support_toWalk, List.tail_cons, List.tail_nil,
        List.mem_singleton] using hx'
    subst x
    exact hzTail hx
  let C := p.append hzb.symm.toWalk
  have hC : C.IsCycle := hp.isCycle_append hzb.symm.isPath_toWalk hDisj
    (Or.inl (by change 1 < L.length + 1; rw [hLen]; omega))
  have hClen : C.length = k := by
    have hpLen : p.length = k - 1 := by
      change L.length + 1 = k - 1
      rw [hLen]
      omega
    change (p.append hzb.symm.toWalk).length = k
    rw [Walk.length_append, hpLen, SimpleGraph.Adj.length_toWalk]
    omega
  have hzC : z ∈ C.support :=
    (Walk.mem_support_append_iff p hzb.symm.toWalk).mpr (Or.inl p.start_mem_support)
  have huC : u.val ∈ C.support :=
    (Walk.mem_support_append_iff p hzb.symm.toWalk).mpr
      (Or.inl (List.mem_cons_of_mem z huL))
  have heq : u.val = z := equality_original_cycle_support_rainbow hk hcrit hcount c
    C hC hClen huC hzC (fun he => hwQ (he ▸ u.property)) hzw huColor
  exact hzQ (heq ▸ u.property)

theorem critical_clique_succ_complete_original (hcrit : IsCriticalPlus k G)
    (S : Finset V) (hS : G.IsClique (S : Set V)) (hcard : S.card = k + 1) :
    IsCompleteOfOrder G (k + 1) := by
  classical
  have hspan : ∀ w : V, w ∈ S := by
    intro w
    by_contra hw
    let f : S → {x : V | x ≠ w} := fun z =>
      ⟨z.val, fun he => hw (he ▸ z.property)⟩
    have hpair : Pairwise (fun i j : S =>
        (G.induce {x | x ≠ w}).Adj (f i) (f j)) := by
      intro i j hij
      exact hS i.property j.property (fun he => hij (Subtype.ext he))
    have hle := (_root_.TaskH.critical_colorable_deletedVertex hcrit w).card_le_of_pairwise_adj f hpair
    have hc : Nat.card S = k + 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hcard]
    omega
  have htop : G = ⊤ := by
    apply G.eq_top_iff_forall_ne_adj.mpr
    intro x y hxy
    exact hS (hspan x) (hspan y) hxy
  have hSu : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hspan
  have hn : Fintype.card V = k + 1 := by
    simpa only [hSu, Finset.card_univ] using hcard
  change Nonempty (G ≃g (⊤ : SimpleGraph (Fin (k + 1))))
  rw [htop]
  exact ⟨SimpleGraph.Iso.completeGraph (Fintype.equivFinOfCardEq hn)⟩

end TaskH.General

#print axioms TaskH.General.equality_original_k_clique_two_exterior_hooks
#print axioms TaskH.General.critical_clique_succ_complete_original
