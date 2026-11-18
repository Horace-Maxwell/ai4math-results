import Research.TaskH.Gao.BicliqueG5DegreeOrder
import Research.TaskH.Gao.BicliqueThirdMatching
import Research.TaskH.Gao.BicliqueTerminalOriginalFamily
import Research.TaskH.Gao.BicliqueLexicographicSelection
import Research.TaskH.Gao.Challenge

/-! Primary635--645. Matching and terminal attachment are derived from the
original counterexample before the actual rooted G5 induction is invoked. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem g5_has_paths_reverse (G : SimpleGraph V) (x y : V) (k : ℕ)
    (h : HasAdmissiblePaths G x y k) : HasAdmissiblePaths G y x k := by
  obtain ⟨a, step, p, hp⟩ := h
  exact ⟨a, step, (fun i => (p i).reverse), (admissible_family_reverse G x y k a step p hp).1⟩

theorem biclique_g5_original_family [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hmax : CasebiLexMax G x y A B)
    (htri : CasebiNoRootTriangle G x y) (hquad : CasebiNoTripleOnRootQuad G x y)
    (hs : 1 ≤ s) (hsk : s ≤ k - 2) (hB : B.ncard = s + 1)
    (hA : s + 2 ≤ A.ncard)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) :
    HasAdmissiblePaths G x y k := by
  classical
  obtain ⟨hAB, hc, hx, hy, _hBtwo, _hBA⟩ := hmax.1
  have hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ (A ∪ B)).ncard ≤ s + 1 := by
    intro d
    have hh := casebi_lexmax_total_neighbor_cap G x y A B hmax htri hquad d.1.1 d.1.2
    omega
  have hcapB : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ B).ncard ≤ s := by
    intro d
    have hh := casebi_lexmax_second_neighbor_cap G x y A B hmax d.1.1 d.1.2
    omega
  have hM := biclique_third_native_matching G A B x y s k C hG hAB hc hx hy hs hsk
    (by omega) hB hNx hNy hcap hd ih hno
  have hMatching := hM
  obtain ⟨d₀, _e₀, u, _v₀, hu, _hv₀, _hde, _huv, edu, _eev⟩ := hMatching
  have hAttach := biclique_singleton_terminal_attachment G A B x y s k C
    hG hAB hc hx hy hs hsk (by omega) hB hNx hNy hd ih hno
  let N := g5Retained G A B y u C
  let S := g5Collapse G A B y u C
  let J := regionIdentificationGraph G N S
  let : Fintype (IdentificationVertex {w : (N ∪ S : Set V) | w.1 ∈ S}) := Fintype.ofFinite _
  have hroot := g5_actual_quotient_rooted G A B y u C hu ⟨d₀, edu⟩ hM hAttach
  have hdegree := g5_actual_nonroot_degree G A B x y u s k C hx hNy (by omega)
    hcap hcapB hd
  have hn := g5_actual_strict_order G A B y u s C hAB hu hy hs hB
  have hn' : Fintype.card (IdentificationVertex {w : (N ∪ S : Set V) | w.1 ∈ S}) <
      Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hn
  let ell := k - s
  have hchild := ih (IdentificationVertex {w : (N ∪ S : Set V) | w.1 ∈ S}) J
    (some (g5Root G A B y u C)) none ell hn' (by dsimp [ell]; omega) hroot hdegree
  have hchild' := g5_has_paths_reverse J (some (g5Root G A B y u C)) none ell hchild
  obtain ⟨a, step, p, hp⟩ := hchild'
  obtain ⟨v, q, hv, hfam, _hlen, hsupp⟩ := identification_induced_family_lift G
    (N ∪ S) S (g5Root G A B y u C) ell a step p hp
  dsimp only [g5Root, regionRetainedVertex] at q hfam
  have hvA : ∀ i : Fin ell, v i ∈ A ∧ v i ≠ u := by
    intro i
    exact ⟨(hv i).1, (hv i).2.1⟩
  have hyt : y ∉ N ∪ S := by
    rintro (hyN | hyS)
    · rcases hyN with hyR | hyu
      · exact hyR.1 (Or.inr rfl)
      · exact hy (Or.inl (hyu.symm ▸ hu))
    · exact hy (Or.inl hyS.1)
  have euy : G.Adj u y := by
    have eyu : G.Adj y u := by
      change u ∈ G.neighborSet y
      rw [hNy]
      exact hu
    exact eyu.symm
  let T : G.Walk u y := euy.toWalk
  have hTP : T.IsPath := euy.isPath_toWalk
  have hTL : T.length = 1 := euy.length_toWalk
  have hqT : ∀ i z, z ∈ (q i).support → z ∈ T.support → z = u := by
    intro i z hz hzT
    rw [SimpleGraph.Adj.support_toWalk] at hzT
    have hh : z = u ∨ z = y := by simpa using hzT
    rcases hh with he | he
    · exact he
    · exact False.elim (hyt
        (Eq.mp (congrArg (fun t : V => t ∈ N ∪ S) he) (hsupp i z hz).1))
  let L : ∀ i : Fin ell, G.Walk y (v i) := fun i => ((q i).append T).reverse
  have hLP : ∀ i, (L i).IsPath := fun i =>
    (append_isPath_of_only_common_endpoint (hfam.2.2 i).1 hTP (hqT i)).reverse
  have hLL : ∀ i, (L i).length = (a + 1) + i.val * step := by
    intro i
    change ((q i).append T).reverse.length = (a + 1) + i.val * step
    rw [Walk.length_reverse, Walk.length_append, hTL, (hfam.2.2 i).2]
    omega
  have hpre : ∀ i : Fin ell, ∃ c : Fin (s + 1) → G.Walk (v i) x,
      ∀ j, (c j).IsPath ∧ (c j).length = 1 + 2 * j.val ∧
        (∀ z ∈ (c j).support, z ∈ A ∨ z ∈ B) ∧ u ∉ (c j).support := by
    intro i
    simpa only [Nat.sub_zero] using biclique_second_odd_prefixes G A B s 0 x (v i) u
      hAB hc (Or.inl ⟨rfl, hA⟩) hB hx (hvA i).1 hu (hvA i).2
  choose c hcP using hpre
  have hmeet : ∀ i j z, z ∈ (L i).support → z ∈ (c i j).support → z = v i := by
    intro i j z hzL hzc
    have hzQ := (hcP i j).2.2.1 z hzc
    have hzu : z ≠ u := by
      intro he
      exact (hcP i j).2.2.2 (Eq.mp (congrArg (fun t : V => t ∈ (c i j).support) he) hzc)
    have hzy : z ≠ y := fun he => hy
      (Eq.mp (congrArg (fun t : V => t ∈ A ∪ B) he) hzQ)
    have hzL' : z ∈ ((q i).append T).support := by
      simpa only [L, Walk.support_reverse, List.mem_reverse] using hzL
    rw [Walk.support_append] at hzL'
    rcases List.mem_append.mp hzL' with hzq | hzT
    · have hh := hsupp i z hzq
      rcases hh.1 with hzN | hzS
      · rcases hzN with hzR | hzu'
        · exact False.elim (hzR.1 (Or.inl hzQ))
        · exact False.elim (hzu hzu')
      · rcases hh.2 with he | he
        · exact he
        · exact False.elim (he hzS)
    · have hzT' : z ∈ T.support := List.mem_of_mem_tail hzT
      rw [SimpleGraph.Adj.support_toWalk] at hzT'
      have hh : z = u ∨ z = y := by simpa using hzT'
      exact False.elim (hh.elim hzu hzy)
  have hyx := admissible_path_concatenation (G := G)
    (by dsimp [ell]; omega : 1 ≤ ell) (by omega : 1 ≤ s + 1)
    (by have ha := hfam.1; omega : 2 ≤ a + 1) (by omega : 1 ≤ (1 : ℕ))
    hfam.2.1 (Or.inr rfl) v L c hLP (fun i j => (hcP i j).1) hLL
    (by intro i j; have hh := (hcP i j).2.1; omega) hmeet
  have hncount : ell + (s + 1) - 1 = k := by dsimp [ell]; omega
  rw [hncount] at hyx
  exact g5_has_paths_reverse G y x k hyx

theorem biclique_g5_actual_outside_component [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hAB : Disjoint A B) (hx : x ∈ B) (hy : y ∉ A ∪ B)
    (hA : A.Nonempty) (hAA : ∀ a ∈ A, ∀ b ∈ A, ¬G.Adj a b)
    (hB : B.ncard = s + 1) (hsk : s + 2 ≤ k)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    Nonempty (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent := by
  classical
  obtain ⟨a, ha⟩ := hA
  have hax : a ≠ x := fun he => Set.disjoint_left.mp hAB ha (he.symm ▸ hx)
  have hay : a ≠ y := fun he => hy (Or.inl (he ▸ ha))
  have hdegree := hd a hax hay
  have hex : ∃ z, G.Adj a z ∧ z ∉ bicliqueSingletonCore A B y := by
    by_contra hno
    have hsub : G.neighborSet a ⊆ B ∪ {y} := by
      intro z ez
      have hzK : z ∈ bicliqueSingletonCore A B y := by
        by_contra hz
        exact hno ⟨z, ez, hz⟩
      rcases hzK with (hzA | hzB) | hzy
      · exact False.elim (hAA a ha z hzA ez)
      · exact Or.inl hzB
      · exact Or.inr hzy
    have hb := Set.ncard_le_ncard hsub
    have hyB : y ∉ B := fun h => hy (Or.inr h)
    rw [Set.union_singleton, Set.ncard_insert_of_notMem hyB, hB] at hb
    omega
  obtain ⟨z, _ez, hz⟩ := hex
  exact ⟨(G.induce (bicliqueSingletonCore A B y)ᶜ).connectedComponentMk ⟨z, hz⟩⟩

theorem biclique_g5_original_balanced [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hG : TwoConnected G) (hmax : CasebiLexMax G x y A B)
    (htri : CasebiNoRootTriangle G x y) (hquad : CasebiNoTripleOnRootQuad G x y)
    (hs : 1 ≤ s) (hsk : s ≤ k - 2) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) : A.ncard = s + 1 := by
  classical
  have hBA := hmax.1.2.2.2.2.2
  have hAlo : s + 1 ≤ A.ncard := by omega
  by_contra hne
  have hA : s + 2 ≤ A.ncard := by omega
  obtain ⟨hAB, _hc, hx, hy, _hBtwo, _hBA⟩ := hmax.1
  have hAA := (casebi_parts_independent G x y A B hmax.1 htri hquad).1
  have hAne : A.Nonempty := (Set.ncard_pos (Set.toFinite A)).mp (by omega)
  obtain ⟨C⟩ := biclique_g5_actual_outside_component G A B x y s k hAB hx hy hAne hAA hB
    (by omega) hd
  exact hno (biclique_g5_original_family G A B x y s k C hG hmax htri hquad hs hsk hB
    hA hNx hNy hd ih hno)

#print axioms g5_has_paths_reverse
#print axioms biclique_g5_original_family
#print axioms biclique_g5_actual_outside_component
#print axioms biclique_g5_original_balanced
end TaskH.Gao
