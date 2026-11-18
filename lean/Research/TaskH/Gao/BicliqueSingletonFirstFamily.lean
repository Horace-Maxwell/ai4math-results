import Research.TaskH.Gao.BicliqueSingletonFirstInduction
import Research.TaskH.Gao.IdentificationFamilyLift
import Research.TaskH.Gao.BipartitePrefixFamily

/-! Only the first singleton-biclique boundary claim, primary580–589. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem biclique_first_even_prefixes [Finite V] (G : SimpleGraph V)
    (A B : Set V) (s : ℕ) (x p u w : V)
    (hs : 2 ≤ s) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hx : x ∈ B) (hp : p ∈ B) (hu : u ∈ B) (hw : w ∈ A)
    (hxp : x ≠ p) (hxu : x ≠ u) (hpu : p ≠ u) :
    ∃ q : Fin (s - 1) → G.Walk p x, ∀ j,
      (q j).IsPath ∧ (q j).length = 2 + 2 * j.val ∧
      (∀ z ∈ (q j).support, z ∈ A ∨ z ∈ B) ∧
      u ∉ (q j).support ∧ w ∉ (q j).support := by
  classical
  let FA := (Set.toFinite A).toFinset.erase w
  let FB := (Set.toFinite B).toFinset.erase u
  have hFA : FA.card = A.ncard - 1 := by
    rw [Finset.card_erase_of_mem ((Set.toFinite A).mem_toFinset.mpr hw),
      ← Set.ncard_eq_toFinset_card A (Set.toFinite A)]
  have hFB : FB.card = B.ncard - 1 := by
    rw [Finset.card_erase_of_mem ((Set.toFinite B).mem_toFinset.mpr hu),
      ← Set.ncard_eq_toFinset_card B (Set.toFinite B)]
  have hdis : Disjoint FA FB := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    exact Set.disjoint_left.mp hAB
      ((Set.toFinite A).mem_toFinset.mp (Finset.mem_of_mem_erase hzA))
      ((Set.toFinite B).mem_toFinset.mp (Finset.mem_of_mem_erase hzB))
  have hcross : ∀ a ∈ FA, ∀ b ∈ FB, G.Adj a b := by
    intro a ha b hb
    exact hc a ((Set.toFinite A).mem_toFinset.mp (Finset.mem_of_mem_erase ha))
      b ((Set.toFinite B).mem_toFinset.mp (Finset.mem_of_mem_erase hb))
  have hxF : x ∈ FB := Finset.mem_erase.mpr ⟨hxu, (Set.toFinite B).mem_toFinset.mpr hx⟩
  have hpF : p ∈ FB := Finset.mem_erase.mpr ⟨hpu, (Set.toFinite B).mem_toFinset.mpr hp⟩
  obtain ⟨q, hq⟩ := bipartite_even_prefix_family FA FB (s - 1) p x hdis hcross
    hpF hxF hxp.symm (by omega) (by omega)
  refine ⟨q, ?_⟩
  intro j
  obtain ⟨hqP, hqL, hqS⟩ := hq j
  refine ⟨hqP, by omega, ?_, ?_, ?_⟩
  · intro z hz
    rcases hqS z hz with hz | hz
    · exact Or.inl ((Set.toFinite A).mem_toFinset.mp (Finset.mem_of_mem_erase hz))
    · exact Or.inr ((Set.toFinite B).mem_toFinset.mp (Finset.mem_of_mem_erase hz))
  · intro hz
    rcases hqS u hz with hz | hz
    · exact Set.disjoint_left.mp hAB
        ((Set.toFinite A).mem_toFinset.mp (Finset.mem_of_mem_erase hz)) hu
    · exact (Finset.notMem_erase u (Set.toFinite B).toFinset) hz
  · intro hz
    rcases hqS w hz with hz | hz
    · exact (Finset.notMem_erase w (Set.toFinite A).toFinset) hz
    · exact Set.disjoint_left.mp hAB hw
        ((Set.toFinite B).mem_toFinset.mp (Finset.mem_of_mem_erase hz))

theorem biclique_singleton_first_boundary_branch [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (hnoA : ¬∃ a ∈ A, ∃ d : C.supp, G.Adj a d.1.1)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  let K := bicliqueSingletonCore A B y
  let R := singletonG1Vertices G K C
  have hbud := biclique_first_two_boundary_forces_s G A B x y s C hG hx hy hs hB hNx hNy hnoA
  have hs2 : 2 ≤ s := hbud.1
  obtain ⟨u, hu⟩ := (Set.ncard_pos (Set.toFinite (singletonG1Boundary G K C))).mp
    (by
      have hh := hbud.2.1
      change 2 ≤ (singletonG1Boundary G K C).ncard at hh
      omega : 0 < (singletonG1Boundary G K C).ncard)
  have hsub := biclique_first_boundary_subset G A B x y C hNx hNy hnoA
  have huB : u ∈ B := (hsub hu).1
  have hux : u ≠ x := (hsub hu).2
  have huBoundary : u ∈ equalBranchBoundary G R := by
    rw [singleton_g1_full_boundary]
    exact hu
  have hchild := biclique_first_family_from_smaller_IH G A B x y u s k C
    hG hx hy hs (by omega) hB hNx hNy hnoA hu hd ih
  let S := equalBranchBoundary G R \ {u}
  let ell := k - s + 2
  obtain ⟨a, d, p, hp⟩ := hchild
  obtain ⟨v, q, hv, hfam, _hlen, hsupp⟩ := identification_induced_family_lift G
    (boundaryDomain G R) S (boundaryRetainedRoot G R u huBoundary) ell a d p hp
  dsimp only [boundaryRetainedRoot] at q hfam
  have hvB : ∀ i : Fin ell, v i ∈ B ∧ v i ≠ x ∧ v i ≠ u := by
    intro i
    have hb : v i ∈ singletonG1Boundary G K C := by
      rw [← singleton_g1_full_boundary]
      exact (hv i).1
    exact ⟨(hsub hb).1, (hsub hb).2, (hv i).2⟩
  obtain ⟨w, hw⟩ := (Set.ncard_pos (Set.toFinite A)).mp (by omega : 0 < A.ncard)
  have hwK : w ∈ K := Or.inl (Or.inl hw)
  have hyK : y ∈ K := Or.inr rfl
  have hwt : w ∉ boundaryDomain G R := by
    rintro (hwR | hwE)
    · exact hwR.1 hwK
    · have hb : w ∈ singletonG1Boundary G K C := by rw [← singleton_g1_full_boundary]; exact hwE
      exact Set.disjoint_left.mp hAB hw (hsub hb).1
  have hyt : y ∉ boundaryDomain G R := by
    rintro (hyR | hyE)
    · exact hyR.1 hyK
    · have hb : y ∈ singletonG1Boundary G K C := by rw [← singleton_g1_full_boundary]; exact hyE
      exact hy (Or.inr (hsub hb).1)
  have euw : G.Adj u w := (hc w hw u huB).symm
  have ewy : G.Adj w y := by
    have eyw : G.Adj y w :=
      Eq.mpr (congrArg (fun S : Set V => w ∈ S) hNy) hw
    exact eyw.symm
  let T : G.Walk u y := Walk.cons euw ewy.toWalk
  have hTP : T.IsPath := by
    apply ewy.isPath_toWalk.cons
    intro hz
    rw [SimpleGraph.Adj.support_toWalk] at hz
    have hz' : u = w ∨ u = y := by simpa using hz
    rcases hz' with he | he
    · exact Set.disjoint_left.mp hAB
        (Eq.mpr (congrArg (fun z : V => z ∈ A) he) hw) huB
    · exact hy (Or.inr (Eq.mp (congrArg (fun z : V => z ∈ B) he) huB))
  have hTL : T.length = 2 := by rw [Walk.length_cons, ewy.length_toWalk]
  have hqT : ∀ i z, z ∈ (q i).support → z ∈ T.support → z = u := by
    intro i z hz hzT
    change z ∈ u :: ewy.toWalk.support at hzT
    rcases List.mem_cons.mp hzT with he | hzT
    · exact he
    · rw [SimpleGraph.Adj.support_toWalk] at hzT
      have hzT' : z = w ∨ z = y := by simpa using hzT
      rcases hzT' with he | he
      · exact False.elim (hwt (Eq.mp (congrArg (fun t : V => t ∈ boundaryDomain G R) he) (hsupp i z hz).1))
      · exact False.elim (hyt (Eq.mp (congrArg (fun t : V => t ∈ boundaryDomain G R) he) (hsupp i z hz).1))
  let L : ∀ i : Fin ell, G.Walk y (v i) := fun i => ((q i).append T).reverse
  have hLP : ∀ i, (L i).IsPath := fun i =>
    (append_isPath_of_only_common_endpoint (hfam.2.2 i).1 hTP (hqT i)).reverse
  have hLL : ∀ i, (L i).length = (a + 2) + i.val * d := by
    intro i
    change ((q i).append T).reverse.length = (a + 2) + i.val * d
    rw [Walk.length_reverse, Walk.length_append, hTL, (hfam.2.2 i).2]
    omega
  have hpre : ∀ i : Fin ell, ∃ c : Fin (s - 1) → G.Walk (v i) x,
      ∀ j, (c j).IsPath ∧ (c j).length = 2 + 2 * j.val ∧
        (∀ z ∈ (c j).support, z ∈ A ∨ z ∈ B) ∧
        u ∉ (c j).support ∧ w ∉ (c j).support := by
    intro i
    exact biclique_first_even_prefixes G A B s x (v i) u w hs2 hAB hc hA hB
      hx (hvB i).1 huB hw (hvB i).2.1.symm hux.symm (hvB i).2.2
  choose c hcP using hpre
  have hmeet : ∀ i j z, z ∈ (L i).support → z ∈ (c i j).support → z = v i := by
    intro i j z hzL hzc
    have hzQ := (hcP i j).2.2.1 z hzc
    have hzu : z ≠ u := by intro he; exact (hcP i j).2.2.2.1 (he ▸ hzc)
    have hzw : z ≠ w := by intro he; exact (hcP i j).2.2.2.2 (he ▸ hzc)
    have hzy : z ≠ y := fun he => hy (Eq.mp (congrArg (fun t : V => t ∈ A ∪ B) he) hzQ)
    have hzA : z ∈ ((q i).append T).support := by
      simpa only [L, Walk.support_reverse, List.mem_reverse] using hzL
    rw [Walk.support_append] at hzA
    rcases List.mem_append.mp hzA with hzq | hzT
    · have hh := hsupp i z hzq
      rcases hh.1 with hzR | hzE
      · exact False.elim (hzR.1 (Or.inl hzQ))
      · rcases hh.2 with he | he
        · exact he
        · exact False.elim (he ⟨hzE, hzu⟩)
    · have hzT' : z ∈ T.support := List.mem_of_mem_tail hzT
      change z ∈ u :: ewy.toWalk.support at hzT'
      rcases List.mem_cons.mp hzT' with he | hzT'
      · exact False.elim (hzu he)
      · rw [SimpleGraph.Adj.support_toWalk] at hzT'
        have hh : z = w ∨ z = y := by simpa using hzT'
        exact False.elim (hh.elim hzw hzy)
  have hyx := admissible_path_concatenation (G := G)
    (by dsimp [ell]; omega : 1 ≤ ell) (by omega : 1 ≤ s - 1)
    (by have ha := hfam.1; omega : 2 ≤ a + 2) (by omega : 1 ≤ (2 : ℕ))
    hfam.2.1 (Or.inr rfl) v L c hLP (fun i j => (hcP i j).1) hLL
    (by intro i j; have hh := (hcP i j).2.1; omega) hmeet
  have hn : ell + (s - 1) - 1 = k := by dsimp [ell]; omega
  rw [hn] at hyx
  obtain ⟨b, e, paths, hpaths⟩ := hyx
  exact ⟨b, e, (fun i => (paths i).reverse), (admissible_family_reverse G y x k b e paths hpaths).1⟩


theorem biclique_singleton_first_boundary [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) :
    ∃ a ∈ A, ∃ d : C.supp, G.Adj a d.1.1 := by
  by_contra hnoA
  exact hno (biclique_singleton_first_boundary_branch G A B x y s k C hG hAB hc
    hx hy hs hsk hA hB hNx hNy hd hnoA ih)

#print axioms biclique_first_even_prefixes
#print axioms biclique_singleton_first_boundary_branch
#print axioms biclique_singleton_first_boundary
end TaskH.Gao
