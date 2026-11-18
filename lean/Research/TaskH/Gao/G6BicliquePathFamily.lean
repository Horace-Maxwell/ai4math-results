import Research.TaskH.Gao.G6TaggedPathLift
import Research.TaskH.Gao.BipartitePrefixFamily

/-! Exact original G6 concatenation. A lifted path may contain w; every
bipartite prefix avoids BOTH u and w. No path shortening is performed. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem g6_biclique_odd_prefixes [Finite V] (G : SimpleGraph V)
    (A B : Set V) (s : ℕ) (x p u w : V)
    (hAB : Disjoint A B) (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hA : A.ncard = s + 1) (hB : B.ncard = s + 1)
    (hx : x ∈ B) (hp : p ∈ A) (hu : u ∈ A) (hw : w ∈ B)
    (hxw : x ≠ w) (hpu : p ≠ u) :
    ∃ q : Fin s → G.Walk p x, ∀ j,
      (q j).IsPath ∧ (q j).length = 1 + 2 * j.val ∧
        (∀ z ∈ (q j).support, z ∈ A ∨ z ∈ B) ∧
          u ∉ (q j).support ∧ w ∉ (q j).support := by
  classical
  let FA := (Set.toFinite A).toFinset
  let FB := (Set.toFinite B).toFinset
  have hFA : FA.card = A.ncard := (Set.ncard_eq_toFinset_card A (Set.toFinite A)).symm
  have hFB : FB.card = B.ncard := (Set.ncard_eq_toFinset_card B (Set.toFinite B)).symm
  have hdis : Disjoint FA FB := by
    apply Finset.disjoint_left.mpr
    intro z ha hb
    exact Set.disjoint_left.mp hAB
      ((Set.toFinite A).mem_toFinset.mp ha) ((Set.toFinite B).mem_toFinset.mp hb)
  have hcross : ∀ a ∈ FA, ∀ b ∈ FB, G.Adj a b := by
    intro a ha b hb
    exact hc a ((Set.toFinite A).mem_toFinset.mp ha) b ((Set.toFinite B).mem_toFinset.mp hb)
  obtain ⟨q, hq⟩ := bipartite_odd_prefix_family_avoid_two FA FB s x p u w hdis hcross
    ((Set.toFinite B).mem_toFinset.mpr hx) ((Set.toFinite A).mem_toFinset.mpr hp)
    ((Set.toFinite A).mem_toFinset.mpr hu) ((Set.toFinite B).mem_toFinset.mpr hw)
    hxw hpu (by omega) (by omega)
  refine ⟨(fun j => (q j).reverse), ?_⟩
  intro j
  obtain ⟨hP, hL, hS, hU, hW⟩ := hq j
  refine ⟨hP.reverse, ?_, ?_, ?_, ?_⟩
  · rw [Walk.length_reverse, hL]
    omega
  · intro z hz
    have hz' : z ∈ (q j).support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hz
    rcases hS z hz' with hzA | hzB
    · exact Or.inl ((Set.toFinite A).mem_toFinset.mp hzA)
    · exact Or.inr ((Set.toFinite B).mem_toFinset.mp hzB)
  · intro hz
    apply hU
    simpa only [Walk.support_reverse, List.mem_reverse] using hz
  · intro hz
    apply hW
    simpa only [Walk.support_reverse, List.mem_reverse] using hz

theorem admissible_family_initial_segment (G : SimpleGraph V) (x y : V)
    (k r : ℕ) (hkr : k ≤ r) (h : HasAdmissiblePaths G x y r) :
    HasAdmissiblePaths G x y k := by
  obtain ⟨a, d, p, hp⟩ := h
  let f : Fin k → Fin r := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hkr⟩
  refine ⟨a, d, (fun i => p (f i)), hp.1, hp.2.1, ?_⟩
  intro i
  exact hp.2.2 (f i)

theorem g6_actual_family_from_quotient [Fintype V] (G : SimpleGraph V)
    (H A B : Set V) (x y u w : V) (s k : ℕ)
    (hAB : Disjoint A B) (hHA : Disjoint H A) (hHB : Disjoint H B)
    (hHy : y ∉ H) (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hu : u ∈ A) (hw : w ∈ B) (hxw : x ≠ w)
    (hA : A.ncard = s + 1) (hB : B.ncard = s + 1)
    (hs : 1 ≤ s) (hsk : s ≤ k)
    (hNy : G.neighborSet y = A)
    (hchild : HasAdmissiblePaths (g6Graph G H A u w)
      (some (Sum.inr false)) none (k - s + 1)) :
    HasAdmissiblePaths G x y k := by
  classical
  have huH : u ∉ H := fun h => Set.disjoint_left.mp hHA h hu
  have hwH : w ∉ H := fun h => Set.disjoint_left.mp hHB h hw
  have hwA : w ∉ A := fun h => Set.disjoint_left.mp hAB h hw
  have huw : u ≠ w := by
    intro he
    exact hwA (Eq.mp (congrArg (fun z : V => z ∈ A) he) hu)
  have hST := g6Boundary_disjoint_retained G H A u w hHA hwA
  let ell := k - s + 1
  obtain ⟨a, d, p, hp⟩ := hchild
  obtain ⟨v, q, hv, hfam, _hlen, hsupp⟩ :=
    g6_tagged_family_lift_to_u G H A u w huH hwH huw hST ell a d p hp
  have euy : G.Adj u y :=
    (show G.Adj y u from Eq.mpr (congrArg (fun L : Set V => u ∈ L) hNy) hu).symm
  let T : G.Walk u y := euy.toWalk
  have hTP : T.IsPath := euy.isPath_toWalk
  have hTL : T.length = 1 := euy.length_toWalk
  have hqT : ∀ i z, z ∈ (q i).support → z ∈ T.support → z = u := by
    intro i z hz hzT
    have he : z = u ∨ z = y := by
      simpa only [T, Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] using hzT
    rcases he with he | he
    · exact he
    · subst z
      rcases hsupp i y hz with hyv | hyT
      · exact False.elim (hy (Or.inl (Eq.mpr
          (congrArg (fun z : V => z ∈ A) hyv) (hv i).1)))
      · rcases hyT with hyH | hyu | hyw
        · exact False.elim (hHy hyH)
        · exact False.elim (hy (Or.inl (Eq.mpr (congrArg (fun z : V => z ∈ A) hyu) hu)))
        · exact False.elim (hy (Or.inr (Eq.mpr (congrArg (fun z : V => z ∈ B) hyw) hw)))
  let L : ∀ i : Fin ell, G.Walk y (v i) := fun i => ((q i).append T).reverse
  have hLP : ∀ i, (L i).IsPath := fun i =>
    (append_isPath_of_only_common_endpoint (hfam.2.2 i).1 hTP (hqT i)).reverse
  have hLL : ∀ i, (L i).length = (a + 1) + i.val * d := by
    intro i
    change ((q i).append T).reverse.length = (a + 1) + i.val * d
    rw [Walk.length_reverse, Walk.length_append, hTL, (hfam.2.2 i).2]
    omega
  have hpre : ∀ i : Fin ell, ∃ c : Fin s → G.Walk (v i) x, ∀ j,
      (c j).IsPath ∧ (c j).length = 1 + 2 * j.val ∧
        (∀ z ∈ (c j).support, z ∈ A ∨ z ∈ B) ∧
          u ∉ (c j).support ∧ w ∉ (c j).support := by
    intro i
    exact g6_biclique_odd_prefixes G A B s x (v i) u w hAB hc hA hB hx
      (hv i).1 hu hw hxw (hv i).2.1
  choose c hcP using hpre
  have hmeet : ∀ i j z, z ∈ (L i).support → z ∈ (c i j).support → z = v i := by
    intro i j z hzL hzc
    have hzQ := (hcP i j).2.2.1 z hzc
    have hzu : z ≠ u := by
      intro he
      exact (hcP i j).2.2.2.1 (Eq.mp (congrArg (fun t : V => t ∈ (c i j).support) he) hzc)
    have hzw : z ≠ w := by
      intro he
      exact (hcP i j).2.2.2.2 (Eq.mp (congrArg (fun t : V => t ∈ (c i j).support) he) hzc)
    have hzy : z ≠ y := fun he => hy
      (Eq.mp (congrArg (fun t : V => t ∈ A ∪ B) he) hzQ)
    have hzL' : z ∈ ((q i).append T).support := by
      simpa only [L, Walk.support_reverse, List.mem_reverse] using hzL
    rw [Walk.support_append] at hzL'
    rcases List.mem_append.mp hzL' with hzq | hzT
    · rcases hsupp i z hzq with he | hzR
      · exact he
      · rcases hzR with hzH | hzu' | hzw'
        · exact False.elim (hzQ.elim (Set.disjoint_left.mp hHA hzH)
            (Set.disjoint_left.mp hHB hzH))
        · exact False.elim (hzu hzu')
        · exact False.elim (hzw hzw')
    · have hzT' : z ∈ T.support := List.mem_of_mem_tail hzT
      have he : z = u ∨ z = y := by
        simpa only [T, Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] using hzT'
      exact False.elim (he.elim hzu hzy)
  have hyx := admissible_path_concatenation (G := G)
    (by dsimp [ell]; omega : 1 ≤ ell) hs
    (by have ha := hfam.1; omega : 2 ≤ a + 1) (by omega : 1 ≤ (1 : ℕ))
    hfam.2.1 (Or.inr rfl) v L c hLP (fun i j => (hcP i j).1) hLL
    (by intro i j; have hh := (hcP i j).2.1; omega) hmeet
  obtain ⟨b, e, paths, hpaths⟩ := admissible_family_initial_segment G y x k
    (ell + s - 1) (by dsimp [ell]; omega) hyx
  exact ⟨b, e, (fun i => (paths i).reverse),
    (admissible_family_reverse G y x k b e paths hpaths).1⟩

#print axioms g6_biclique_odd_prefixes
#print axioms admissible_family_initial_segment
#print axioms g6_actual_family_from_quotient
end TaskH.Gao
