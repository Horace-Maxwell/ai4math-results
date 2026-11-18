import Research.TaskH.Gao.BicliqueThirdQuotientInduction
import Research.TaskH.Gao.IdentificationFamilyLift
import Research.TaskH.Gao.BipartitePrefixFamily

/-! The real one-edge/two-edge tail and the actual Q-w even prefixes. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem biclique_third_even_prefixes [Finite V] (G : SimpleGraph V)
    (A B : Set V) (x p w : V) (s : ℕ)
    (hAB : Disjoint A B) (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hx : x ∈ B) (hp : p ∈ B) (hxp : x ≠ p) (hw : w ∈ A) :
    ∃ q : Fin s → G.Walk p x, ∀ j,
      (q j).IsPath ∧ (q j).length = 2 + 2 * j.val ∧
      (∀ z ∈ (q j).support, z ∈ A ∨ z ∈ B) ∧ w ∉ (q j).support := by
  classical
  let FA := (Set.toFinite A).toFinset.erase w
  let FB := (Set.toFinite B).toFinset
  have hFA : FA.card = A.ncard - 1 := by
    rw [Finset.card_erase_of_mem ((Set.toFinite A).mem_toFinset.mpr hw),
      ← Set.ncard_eq_toFinset_card A (Set.toFinite A)]
  have hFB : FB.card = B.ncard := (Set.ncard_eq_toFinset_card B (Set.toFinite B)).symm
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
  obtain ⟨q, hq⟩ := bipartite_even_prefix_family FA FB s p x hdis hcross
    ((Set.toFinite B).mem_toFinset.mpr hp) ((Set.toFinite B).mem_toFinset.mpr hx)
    hxp.symm (by omega) (by omega)
  refine ⟨q, ?_⟩
  intro j
  obtain ⟨hqP, hqL, hqS⟩ := hq j
  refine ⟨hqP, by omega, ?_, ?_⟩
  · intro z hz
    rcases hqS z hz with hzA | hzB
    · exact Or.inl ((Set.toFinite A).mem_toFinset.mp (Finset.mem_of_mem_erase hzA))
    · exact Or.inr ((Set.toFinite B).mem_toFinset.mp hzB)
  · intro hz
    rcases hqS w hz with hzA | hzB
    · exact (Finset.notMem_erase w (Set.toFinite A).toFinset) hzA
    · exact Set.disjoint_left.mp hAB hw ((Set.toFinite B).mem_toFinset.mp hzB)

theorem biclique_third_real_tail (G : SimpleGraph V) (u w y : V)
    (huy : u ≠ y) (ewy : G.Adj w y) (hlink : u = w ∨ G.Adj u w) :
    ∃ t : ℕ, ∃ T : G.Walk u y, T.IsPath ∧ T.length = t ∧
      (t = 1 ∨ t = 2) ∧ ∀ z ∈ T.support, z = u ∨ z = w ∨ z = y := by
  rcases hlink with he | euw
  · subst u
    refine ⟨1, ewy.toWalk, ewy.isPath_toWalk, ewy.length_toWalk, Or.inl rfl, ?_⟩
    intro z hz
    rw [SimpleGraph.Adj.support_toWalk] at hz
    have hh : z = w ∨ z = y := by simpa using hz
    exact hh.elim (fun he => Or.inl he) (fun he => Or.inr (Or.inr he))
  · let T : G.Walk u y := Walk.cons euw ewy.toWalk
    have hTP : T.IsPath := by
      apply ewy.isPath_toWalk.cons
      intro hz
      rw [SimpleGraph.Adj.support_toWalk] at hz
      have hh : u = w ∨ u = y := by simpa using hz
      exact hh.elim euw.ne huy
    refine ⟨2, T, hTP, ?_, Or.inr rfl, ?_⟩
    · rw [Walk.length_cons, ewy.length_toWalk]
    · intro z hz
      change z ∈ u :: ewy.toWalk.support at hz
      rcases List.mem_cons.mp hz with he | hz
      · exact Or.inl he
      · rw [SimpleGraph.Adj.support_toWalk] at hz
        have hh : z = w ∨ z = y := by simpa using hz
        exact Or.inr hh

theorem biclique_third_original_family [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u w : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hw : w ∈ A)
    (hs : 1 ≤ s) (hsk : s ≤ k - 2) (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ (A ∪ B)).ncard ≤ s + 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (hcase : BicliqueThirdRootCase G A B y u C)
    (hBtouch : (bicliqueThirdCollapse G A B x y C).Nonempty)
    (hlink : u = w ∨
      (u ∈ singletonG1Vertices G (bicliqueSingletonCore A B y) C ∧ G.Adj u w))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  let K := bicliqueSingletonCore A B y
  let R := singletonG1Vertices G K C
  let N := bicliqueThirdRetained G A B y u C
  let S := bicliqueThirdCollapse G A B x y C
  let ell := k - s + 1
  have hchild := biclique_third_quotient_family_from_smaller_IH G A B x y u s k C hG hAB hx hy
    hs hsk hB hNx hNy hcap hd hcase hBtouch ih
  obtain ⟨a, d, paths, hpaths⟩ := hchild
  obtain ⟨v, q, hv, hfam, _hlen, hsupp⟩ := identification_induced_family_lift G
    (N ∪ S) S (regionRetainedVertex N S (biclique_third_disjoint G A B x y u C hAB hcase)
      ⟨u, Or.inr rfl⟩) ell a d paths hpaths
  dsimp only [regionRetainedVertex] at q hfam
  have hvB : ∀ i : Fin ell, v i ∈ B ∧ v i ≠ x := fun i => (hv i).1
  have huy : u ≠ y := by
    rcases hlink with he | ⟨huR, _⟩
    · intro huy
      have hwy : w = y := he.symm.trans huy
      exact hy (Or.inl (Eq.mp (congrArg (fun z : V => z ∈ A) hwy) hw))
    · intro he
      exact huR.1 (Eq.mpr (congrArg (fun z : V => z ∈ K) he) (Or.inr rfl))
  have ewy : G.Adj w y := by
    have eyw : G.Adj y w :=
      Eq.mpr (congrArg (fun L : Set V => w ∈ L) hNy) hw
    exact eyw.symm
  obtain ⟨t, T, hTP, hTL, ht, hTS⟩ := biclique_third_real_tail G u w y huy ewy
    (hlink.elim Or.inl (fun h => Or.inr h.2))
  have hyt : y ∉ N ∪ S := by
    rintro ((hyR | hyU) | hyS)
    · exact hyR.1 (Or.inr rfl)
    · exact huy hyU.symm
    · exact hy (Or.inr hyS.1.1)
  have hqT : ∀ i z, z ∈ (q i).support → z ∈ T.support → z = u := by
    intro i z hz hzT
    rcases hTS z hzT with he | he | he
    · exact he
    · rcases hlink with huw | ⟨huR, _euw⟩
      · exact he.trans huw.symm
      · have hwN : w ∉ N := by
          rintro (hwR | hwU)
          · exact hwR.1 (Or.inl (Or.inl hw))
          · exact huR.1 (Eq.mp (congrArg (fun z : V => z ∈ K) hwU) (Or.inl (Or.inl hw)))
        have hwS : w ∉ S := fun hh => Set.disjoint_left.mp hAB hw hh.1.1
        have hzD := (hsupp i z hz).1
        have hwD : w ∈ N ∪ S := Eq.mp (congrArg (fun z : V => z ∈ N ∪ S) he) hzD
        exact False.elim (hwD.elim hwN hwS)
    · exact False.elim (hyt
        (Eq.mp (congrArg (fun z : V => z ∈ N ∪ S) he) (hsupp i z hz).1))
  let L : ∀ i : Fin ell, G.Walk y (v i) := fun i => ((q i).append T).reverse
  have hLP : ∀ i, (L i).IsPath := fun i =>
    (append_isPath_of_only_common_endpoint (hfam.2.2 i).1 hTP (hqT i)).reverse
  have hLL : ∀ i, (L i).length = (a + t) + i.val * d := by
    intro i
    change ((q i).append T).reverse.length = (a + t) + i.val * d
    rw [Walk.length_reverse, Walk.length_append, hTL, (hfam.2.2 i).2]
    omega
  have hpre : ∀ i : Fin ell, ∃ c : Fin s → G.Walk (v i) x,
      ∀ j, (c j).IsPath ∧ (c j).length = 2 + 2 * j.val ∧
        (∀ z ∈ (c j).support, z ∈ A ∨ z ∈ B) ∧ w ∉ (c j).support := by
    intro i
    exact biclique_third_even_prefixes G A B x (v i) w s hAB hc hA hB hx (hvB i).1
      (hvB i).2.symm hw
  choose c hcP using hpre
  have hmeet : ∀ i j z, z ∈ (L i).support → z ∈ (c i j).support → z = v i := by
    intro i j z hzL hzc
    have hzQ := (hcP i j).2.2.1 z hzc
    have hzw : z ≠ w := by
      intro he
      exact (hcP i j).2.2.2 (Eq.mp (congrArg (fun v : V => v ∈ (c i j).support) he) hzc)
    have hzu : z ≠ u := by
      rcases hlink with he | ⟨huR, _⟩
      · intro hzu; exact hzw (hzu.trans he)
      · intro he
        exact huR.1 (Or.inl (Eq.mp (congrArg (fun v : V => v ∈ A ∪ B) he) hzQ))
    have hzy : z ≠ y := fun he => hy
      (Eq.mp (congrArg (fun v : V => v ∈ A ∪ B) he) hzQ)
    have hzL' : z ∈ ((q i).append T).support := by
      simpa only [L, Walk.support_reverse, List.mem_reverse] using hzL
    rw [Walk.support_append] at hzL'
    rcases List.mem_append.mp hzL' with hzq | hzT
    · have hh := hsupp i z hzq
      rcases hh.1 with (hzR | hzU) | hzS
      · exact False.elim (hzR.1 (Or.inl hzQ))
      · exact False.elim (hzu hzU)
      · rcases hh.2 with he | he
        · exact he
        · exact False.elim (he hzS)
    · have hzT' : z ∈ T.support := List.mem_of_mem_tail hzT
      exact False.elim ((hTS z hzT').elim hzu (fun h => h.elim hzw hzy))
  have hyx := admissible_path_concatenation (G := G)
    (by dsimp [ell]; omega : 1 ≤ ell) hs
    (by have ha := hfam.1; omega : 2 ≤ a + t) (by omega : 1 ≤ (2 : ℕ))
    hfam.2.1 (Or.inr rfl) v L c hLP (fun i j => (hcP i j).1) hLL
    (by intro i j; have hh := (hcP i j).2.1; omega) hmeet
  have hn : ell + s - 1 = k := by dsimp [ell]; omega
  rw [hn] at hyx
  obtain ⟨b, e, ps, hps⟩ := hyx
  exact ⟨b, e, (fun i => (ps i).reverse), (admissible_family_reverse G y x k b e ps hps).1⟩

#print axioms biclique_third_even_prefixes
#print axioms biclique_third_real_tail
#print axioms biclique_third_original_family
end TaskH.Gao
