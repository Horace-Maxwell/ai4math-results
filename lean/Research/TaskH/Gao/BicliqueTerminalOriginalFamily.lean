import Research.TaskH.Gao.BicliqueTerminalInduction
import Research.TaskH.Gao.BicliqueSingletonFirstFamily
import Research.TaskH.Gao.IdentificationFamilyLift
import Research.TaskH.Gao.BipartitePrefixFamily

/-! The genuine complement tail, variable endpoints and exact original G4 contradiction. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem g4_even_prefixes [Finite V] (G : SimpleGraph V) (A B : Set V)
    (x p a : V) (s : ℕ) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hx : x ∈ B) (hp : p ∈ B) (hxp : x ≠ p) (ha : a ∈ A) :
    ∃ q : Fin s → G.Walk p x, ∀ j,
      (q j).IsPath ∧ (q j).length = 2 + 2 * j.val ∧
      (∀ z ∈ (q j).support, z ∈ A ∨ z ∈ B) ∧ a ∉ (q j).support := by
  classical
  let FA := (Set.toFinite A).toFinset.erase a
  let FB := (Set.toFinite B).toFinset
  have hFA : FA.card = A.ncard - 1 := by
    rw [Finset.card_erase_of_mem ((Set.toFinite A).mem_toFinset.mpr ha),
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
    rcases hqS a hz with hzA | hzB
    · exact (Finset.notMem_erase a (Set.toFinite A).toFinset) hzA
    · exact Set.disjoint_left.mp hAB ha ((Set.toFinite B).mem_toFinset.mp hzB)

theorem g4_actual_complement_tail (G : SimpleGraph V) (A B : Set V) (x y a : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b d : C.supp) (hT : TerminalFragment C.toSimpleGraph I b)
    (hAB : Disjoint A B) (hy : y ∉ A ∪ B) (ha : a ∈ A) (ead : G.Adj a d.1.1)
    (hNy : G.neighborSet y = A)
    (hnoA : ∀ d ∈ I, ∀ a ∈ A, ¬G.Adj (componentVertex C d) a) :
    ∃ T : G.Walk y (componentVertex C b), T.IsPath ∧
      (∀ z ∈ T.support, z ∈ A ∪ B → z = a) ∧
      ∀ z ∈ T.support,
        z ∈ g4Block G A B y C I b ∪ g4Boundary G A B x y C I → z = componentVertex C b := by
  have hdI : d ∉ I := fun hdI => hnoA d hdI a ha ead.symm
  obtain ⟨R, hRP, hRK, hRN⟩ := terminal_component_original_tail C I b d hT hdI
  have haK : a ∈ bicliqueSingletonCore A B y := Or.inl (Or.inl ha)
  have hyK : y ∈ bicliqueSingletonCore A B y := Or.inr rfl
  have haR : a ∉ R.reverse.support := by
    intro hh
    have hh' : a ∈ R.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hh
    exact hRK a hh' haK
  let F : G.Walk a (componentVertex C b) := Walk.cons ead R.reverse
  have hFP : F.IsPath := hRP.reverse.cons haR
  have hyF : y ∉ F.support := by
    intro hz
    change y ∈ a :: R.reverse.support at hz
    rcases List.mem_cons.mp hz with he | hz
    · exact hy (Or.inl (Eq.mpr (congrArg (fun z : V => z ∈ A) he) ha))
    · have hz' : y ∈ R.support := by simpa only [Walk.support_reverse, List.mem_reverse] using hz
      exact hRK y hz' hyK
  have eya : G.Adj y a :=
    Eq.mpr (congrArg (fun S : Set V => a ∈ S) hNy) ha
  let T : G.Walk y (componentVertex C b) := Walk.cons eya F
  have hTP : T.IsPath := hFP.cons hyF
  have hpoints : ∀ z ∈ T.support, z = y ∨ z = a ∨ z ∈ R.support := by
    intro z hz
    change z ∈ y :: a :: R.reverse.support at hz
    rcases List.mem_cons.mp hz with he | hz
    · exact Or.inl he
    · rcases List.mem_cons.mp hz with he | hz
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (by simpa only [Walk.support_reverse, List.mem_reverse] using hz))
  refine ⟨T, hTP, ?_, ?_⟩
  · intro z hz hzQ
    rcases hpoints z hz with he | he | hzR
    · exact False.elim (hy (Eq.mp (congrArg (fun v : V => v ∈ A ∪ B) he) hzQ))
    · exact he
    · exact False.elim (hRK z hzR (Or.inl hzQ))
  · intro z hz hzD
    rcases hpoints z hz with he | he | hzR
    · have hyD : y ∈ g4Block G A B y C I b ∪ g4Boundary G A B x y C I :=
        Eq.mp (congrArg (fun v : V => v ∈ g4Block G A B y C I b ∪ g4Boundary G A B x y C I) he) hzD
      rcases hyD with hyN | hyS
      · exact False.elim (Set.disjoint_left.mp (g4_block_disjoint_core G A B y C I b) hyN hyK)
      · exact False.elim (hy (Or.inr hyS.1.1))
    · have haD : a ∈ g4Block G A B y C I b ∪ g4Boundary G A B x y C I :=
        Eq.mp (congrArg (fun v : V => v ∈ g4Block G A B y C I b ∪ g4Boundary G A B x y C I) he) hzD
      rcases haD with haN | haS
      · exact False.elim (Set.disjoint_left.mp (g4_block_disjoint_core G A B y C I b) haN haK)
      · exact False.elim (Set.disjoint_left.mp hAB ha haS.1.1)
    · rcases hzD with hzN | hzS
      · exact hRN z hzR hzN
      · exact False.elim (hRK z hzR (Or.inl (Or.inr hzS.1.1)))

theorem g4_original_family [Fintype V] (G : SimpleGraph V) (A B : Set V)
    (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b)
    (hG : TwoConnected G) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoA : ∀ d ∈ I, ∀ a ∈ A, ¬G.Adj (componentVertex C d) a)
    (hAtouch : ∃ a ∈ A, ∃ d : C.supp, G.Adj a d.1.1)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  let N := g4Block G A B y C I b
  let S := g4Boundary G A B x y C I
  let ell := k - s + 1
  have hchild := g4_family_from_strict_IH G A B x y s k C I b hT hG hx hy hs hsk hB
    hNx hNy hnoA hd ih
  obtain ⟨a₀, step, ps, hps⟩ := hchild
  obtain ⟨v, q, hv, hfam, _hlen, hsupp⟩ := identification_induced_family_lift G
    (N ∪ S) S (regionRetainedVertex N S (g4_block_boundary_disjoint G A B x y C I b)
      ⟨componentVertex C b, g4_root_mem G A B y C I b⟩) ell a₀ step ps hps
  dsimp only [regionRetainedVertex] at q hfam
  obtain ⟨a, ha, d, ead⟩ := hAtouch
  obtain ⟨T, hTP, hTQ, hTD⟩ := g4_actual_complement_tail G A B x y a C I b d hT hAB hy ha ead hNy hnoA
  have hmeetT : ∀ i z, z ∈ T.support → z ∈ (q i).reverse.support → z = componentVertex C b := by
    intro i z hzT hzq
    have hzq' : z ∈ (q i).support := by simpa only [Walk.support_reverse, List.mem_reverse] using hzq
    exact hTD z hzT (hsupp i z hzq').1
  let L : ∀ i : Fin ell, G.Walk y (v i) := fun i => T.append (q i).reverse
  have hLP : ∀ i, (L i).IsPath := fun i =>
    append_isPath_of_only_common_endpoint hTP (hfam.2.2 i).1.reverse (hmeetT i)
  have hLL : ∀ i, (L i).length = (T.length + a₀) + i.val * step := by
    intro i
    change (T.append (q i).reverse).length = (T.length + a₀) + i.val * step
    rw [Walk.length_append, Walk.length_reverse, (hfam.2.2 i).2]
    omega
  have hpre : ∀ i : Fin ell, ∃ c : Fin s → G.Walk (v i) x,
      ∀ j, (c j).IsPath ∧ (c j).length = 2 + 2 * j.val ∧
        (∀ z ∈ (c j).support, z ∈ A ∨ z ∈ B) ∧ a ∉ (c j).support := by
    intro i
    exact g4_even_prefixes G A B x (v i) a s hAB hc hA hB hx (hv i).1.1
      (by intro h; exact (hv i).1.2 (Set.mem_singleton_iff.mpr h.symm)) ha
  choose c hcP using hpre
  have hmeet : ∀ i j z, z ∈ (L i).support → z ∈ (c i j).support → z = v i := by
    intro i j z hzL hzc
    have hzQ := (hcP i j).2.2.1 z hzc
    have hza : z ≠ a := by
      intro he
      exact (hcP i j).2.2.2 (Eq.mp (congrArg (fun v : V => v ∈ (c i j).support) he) hzc)
    have hzL' : z ∈ T.support ++ (q i).reverse.support.tail := by
      simpa only [L, Walk.support_append] using hzL
    rcases List.mem_append.mp hzL' with hzT | hzq
    · exact False.elim (hza (hTQ z hzT hzQ))
    · have hzq' : z ∈ (q i).support := by
        have hh := List.mem_of_mem_tail hzq
        simpa only [Walk.support_reverse, List.mem_reverse] using hh
      have hh := hsupp i z hzq'
      rcases hh.1 with hzN | hzS
      · exact False.elim (Set.disjoint_left.mp (g4_block_disjoint_core G A B y C I b) hzN (Or.inl hzQ))
      · rcases hh.2 with he | he
        · exact he
        · exact False.elim (he hzS)
  have hyx := admissible_path_concatenation (G := G)
    (by dsimp [ell]; omega : 1 ≤ ell) hs
    (by have ha₀ := hfam.1; omega : 2 ≤ T.length + a₀) (by omega : 1 ≤ (2 : ℕ))
    hfam.2.1 (Or.inr rfl) v L c hLP (fun i j => (hcP i j).1) hLL
    (by intro i j; have hh := (hcP i j).2.1; omega) hmeet
  have hn : ell + s - 1 = k := by dsimp [ell]; omega
  rw [hn] at hyx
  obtain ⟨a', step', paths, hpaths⟩ := hyx
  exact ⟨a', step', (fun i => (paths i).reverse),
    (admissible_family_reverse G y x k a' step' paths hpaths).1⟩

theorem biclique_singleton_terminal_attachment [Fintype V] (G : SimpleGraph V)
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
    ∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
      ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a := by
  intro I b hT
  by_contra hn
  have hnoA : ∀ d ∈ I, ∀ a ∈ A, ¬G.Adj (componentVertex C d) a := by
    intro d hdI a ha e
    exact hn ⟨d, hdI, a, ha, e⟩
  have hAtouch := biclique_singleton_first_boundary G A B x y s k C hG hAB hc hx hy hs hsk
    hA hB hNx hNy hd ih hno
  exact hno (g4_original_family G A B x y s k C I b hT hG hAB hc hx hy hs hsk hA hB
    hNx hNy hnoA hAtouch hd ih)

#print axioms g4_even_prefixes
#print axioms g4_actual_complement_tail
#print axioms g4_original_family
#print axioms biclique_singleton_terminal_attachment
end TaskH.Gao
