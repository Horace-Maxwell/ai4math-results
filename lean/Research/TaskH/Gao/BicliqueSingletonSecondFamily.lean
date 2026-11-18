import Research.TaskH.Gao.BicliqueSingletonSecondInduction
import Research.TaskH.Gao.IdentificationFamilyLift
import Research.TaskH.Gao.BipartitePrefixFamily

/-! Only the second singleton-biclique boundary claim, primary591–602. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem biclique_second_odd_prefixes [Finite V] (G : SimpleGraph V)
    (A B : Set V) (s eps : ℕ) (x p u : V)
    (hAB : Disjoint A B) (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (heps : (eps = 0 ∧ s + 2 ≤ A.ncard) ∨ (eps = 1 ∧ A.ncard = s + 1))
    (hB : B.ncard = s + 1) (hx : x ∈ B) (hp : p ∈ A) (hu : u ∈ A)
    (hpu : p ≠ u) :
    ∃ q : Fin (s + 1 - eps) → G.Walk p x, ∀ j,
      (q j).IsPath ∧ (q j).length = 1 + 2 * j.val ∧
      (∀ z ∈ (q j).support, z ∈ A ∨ z ∈ B) ∧ u ∉ (q j).support := by
  classical
  let FA := (Set.toFinite A).toFinset.erase u
  let FB := (Set.toFinite B).toFinset
  have hFA : FA.card = A.ncard - 1 := by
    rw [Finset.card_erase_of_mem ((Set.toFinite A).mem_toFinset.mpr hu),
      ← Set.ncard_eq_toFinset_card A (Set.toFinite A)]
  have hFB : FB.card = B.ncard := (Set.ncard_eq_toFinset_card B (Set.toFinite B)).symm
  have hAc : s + 1 - eps ≤ FA.card := by
    rcases heps with ⟨he, hA⟩ | ⟨he, hA⟩ <;> omega
  have hBc : s + 1 - eps ≤ FB.card := by omega
  have hdis : Disjoint FA FB := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    exact Set.disjoint_left.mp hAB
      ((Set.toFinite A).mem_toFinset.mp (Finset.mem_of_mem_erase hzA))
      ((Set.toFinite B).mem_toFinset.mp hzB)
  have hcross : ∀ a ∈ FA, ∀ b ∈ FB, G.Adj a b := by
    intro a ha b hb
    exact hc a ((Set.toFinite A).mem_toFinset.mp (Finset.mem_of_mem_erase ha))
      b ((Set.toFinite B).mem_toFinset.mp hb)
  have hxF : x ∈ FB := (Set.toFinite B).mem_toFinset.mpr hx
  have hpF : p ∈ FA := Finset.mem_erase.mpr ⟨hpu, (Set.toFinite A).mem_toFinset.mpr hp⟩
  obtain ⟨q, hq⟩ := bipartite_odd_prefix_family FA FB (s + 1 - eps) x p
    hdis hcross hxF hpF hAc hBc
  refine ⟨(fun j => (q j).reverse), ?_⟩
  intro j
  obtain ⟨hqP, hqL, hqS⟩ := hq j
  refine ⟨hqP.reverse, ?_, ?_, ?_⟩
  · rw [Walk.length_reverse, hqL]
    omega
  · intro z hz
    have hz' : z ∈ (q j).support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hz
    rcases hqS z hz' with hzA | hzB
    · exact Or.inl ((Set.toFinite A).mem_toFinset.mp (Finset.mem_of_mem_erase hzA))
    · exact Or.inr ((Set.toFinite B).mem_toFinset.mp hzB)
  · intro hz
    have hz' : u ∈ (q j).support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hz
    rcases hqS u hz' with hzA | hzB
    · exact (Finset.notMem_erase u (Set.toFinite A).toFinset) hzA
    · exact Set.disjoint_left.mp hAB hu ((Set.toFinite B).mem_toFinset.mp hzB)

theorem biclique_singleton_second_boundary_branch [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ A).ncard ≤ s + 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (hnoB : ¬∃ b ∈ B \ {x}, ∃ d : C.supp, G.Adj b d.1.1)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  let K := bicliqueSingletonCore A B y
  let R := singletonG1Vertices G K C
  let eps : ℕ := if A.ncard = s + 1 then 1 else 0
  have heps : (eps = 0 ∧ s + 2 ≤ A.ncard) ∨ (eps = 1 ∧ A.ncard = s + 1) :=
    biclique_second_size_cases A s hA
  have heps01 : eps = 0 ∨ eps = 1 := heps.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hK := biclique_first_core_card A B y s hy hs hB
  change 3 ≤ K.ncard at hK
  have htwo := singleton_g1_boundary_ncard_ge_two G K C x hG
    (Or.inl (Or.inr hx)) (by omega)
  obtain ⟨u, hu⟩ := (Set.ncard_pos (Set.toFinite (singletonG1Boundary G K C))).mp
    (by omega : 0 < (singletonG1Boundary G K C).ncard)
  have hsub := biclique_second_boundary_subset G A B x y C hNx hNy hnoB
  have huA : u ∈ A := hsub hu
  have huBoundary : u ∈ equalBranchBoundary G R := by
    rw [singleton_g1_full_boundary]
    exact hu
  have hchild := biclique_second_family_from_smaller_IH G A B x y u s k eps C
    hG hx hy hs hsk hB heps hNx hNy hnoB hu hcap hd ih
  let S := equalBranchBoundary G R \ {u}
  let ell := k - s + eps
  let count := s + 1 - eps
  obtain ⟨a, d, p, hp⟩ := hchild
  obtain ⟨v, q, hv, hfam, _hlen, hsupp⟩ := identification_induced_family_lift G
    (boundaryDomain G R) S (boundaryRetainedRoot G R u huBoundary) ell a d p hp
  dsimp only [boundaryRetainedRoot] at q hfam
  have hvA : ∀ i : Fin ell, v i ∈ A ∧ v i ≠ u := by
    intro i
    have hb : v i ∈ singletonG1Boundary G K C := by
      rw [← singleton_g1_full_boundary]
      exact (hv i).1
    exact ⟨hsub hb, (hv i).2⟩
  have hyK : y ∈ K := Or.inr rfl
  have hyt : y ∉ boundaryDomain G R := by
    rintro (hyR | hyE)
    · exact hyR.1 hyK
    · have hb : y ∈ singletonG1Boundary G K C := by
        rw [← singleton_g1_full_boundary]
        exact hyE
      exact hy (Or.inl (hsub hb))
  have euy : G.Adj u y := by
    have eyu : G.Adj y u :=
      Eq.mpr (congrArg (fun L : Set V => u ∈ L) hNy) huA
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
        (Eq.mp (congrArg (fun t : V => t ∈ boundaryDomain G R) he) (hsupp i z hz).1))
  let L : ∀ i : Fin ell, G.Walk y (v i) := fun i => ((q i).append T).reverse
  have hLP : ∀ i, (L i).IsPath := fun i =>
    (append_isPath_of_only_common_endpoint (hfam.2.2 i).1 hTP (hqT i)).reverse
  have hLL : ∀ i, (L i).length = (a + 1) + i.val * d := by
    intro i
    change ((q i).append T).reverse.length = (a + 1) + i.val * d
    rw [Walk.length_reverse, Walk.length_append, hTL, (hfam.2.2 i).2]
    omega
  have hpre : ∀ i : Fin ell, ∃ c : Fin count → G.Walk (v i) x,
      ∀ j, (c j).IsPath ∧ (c j).length = 1 + 2 * j.val ∧
        (∀ z ∈ (c j).support, z ∈ A ∨ z ∈ B) ∧ u ∉ (c j).support := by
    intro i
    exact biclique_second_odd_prefixes G A B s eps x (v i) u hAB hc heps hB hx
      (hvA i).1 huA (hvA i).2
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
      rcases hh.1 with hzR | hzE
      · exact False.elim (hzR.1 (Or.inl hzQ))
      · rcases hh.2 with he | he
        · exact he
        · exact False.elim (he ⟨hzE, hzu⟩)
    · have hzT' : z ∈ T.support := List.mem_of_mem_tail hzT
      rw [SimpleGraph.Adj.support_toWalk] at hzT'
      have hh : z = u ∨ z = y := by simpa using hzT'
      exact False.elim (hh.elim hzu hzy)
  have hyx := admissible_path_concatenation (G := G)
    (by dsimp [ell]; omega : 1 ≤ ell) (by dsimp [count]; omega : 1 ≤ count)
    (by have ha := hfam.1; omega : 2 ≤ a + 1) (by omega : 1 ≤ (1 : ℕ))
    hfam.2.1 (Or.inr rfl) v L c hLP (fun i j => (hcP i j).1) hLL
    (by intro i j; have hh := (hcP i j).2.1; omega) hmeet
  have hn : ell + count - 1 = k := by dsimp [ell, count]; omega
  rw [hn] at hyx
  obtain ⟨b, e, paths, hpaths⟩ := hyx
  exact ⟨b, e, (fun i => (paths i).reverse), (admissible_family_reverse G y x k b e paths hpaths).1⟩

theorem biclique_singleton_second_boundary [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ A).ncard ≤ s + 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) :
    ∃ b ∈ B \ {x}, ∃ d : C.supp, G.Adj b d.1.1 := by
  by_contra hnoB
  exact hno (biclique_singleton_second_boundary_branch G A B x y s k C hG hAB hc
    hx hy hs hsk hA hB hNx hNy hcap hd hnoB ih)

theorem biclique_singleton_second_boundary_from_maximal_biclique [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hmax : ∀ L M : Set V, Disjoint L M →
      (∀ a ∈ L, ∀ b ∈ M, G.Adj a b) → x ∈ M → y ∉ L ∪ M →
      2 ≤ M.ncard → M.ncard ≤ L.ncard → M.ncard ≤ B.ncard)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) :
    ∃ b ∈ B \ {x}, ∃ d : C.supp, G.Adj b d.1.1 := by
  have hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ A).ncard ≤ s + 1 := by
    intro d
    exact biclique_maximal_second_part_neighbor_cap G A B x y s hAB hc hx hy hB
      hmax d.1.1 d.1.2
  exact biclique_singleton_second_boundary G A B x y s k C hG hAB hc hx hy hs hsk
    hA hB hNx hNy hcap hd ih hno

#print axioms biclique_second_odd_prefixes
#print axioms biclique_singleton_second_boundary_branch
#print axioms biclique_singleton_second_boundary
#print axioms biclique_singleton_second_boundary_from_maximal_biclique
end TaskH.Gao
