import Research.TaskH.Gao.SingletonG1Degree
import Research.TaskH.Gao.IdentificationFamilyLift
import Research.TaskH.Gao.CliquePaths

/-! Genuine strict vertex IH and a varying-endpoint actual G1 family contradiction, including t=3. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem singleton_g1_family_from_smaller_IH [Fintype V] (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (x y v : V) (k : ℕ)
    (hG : TwoConnected G) (hx : x ∈ K) (hy : y ∉ K) (ht : 3 ≤ K.ncard)
    (htk : K.ncard ≤ k)
    (hother : C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩)
    (hv : v ∈ singletonG1Boundary G K C)
    (hxD : ¬∃ d : C.supp, G.Adj x d.1.1)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) (s t : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected H s t →
        NonrootDegreeAtLeast H s t (ell + 1) → HasAdmissiblePaths H s t ell) :
    HasAdmissiblePaths (boundaryQuotient G (singletonG1Vertices G K C) v) none
      (some (boundaryRetainedRoot G (singletonG1Vertices G K C) v
        (by rw [singleton_g1_full_boundary G K C]; exact hv))) (k - K.ncard + 3) := by
  classical
  let R := singletonG1Vertices G K C
  let : Fintype (IdentificationVertex (boundaryCollapse G R v)) := singletonG1Fintype G K C v
  have hroot := singleton_g1_rooted G K C x v hG hx (by omega : 2 ≤ K.ncard) hv
  have hd := singleton_g1_nonroot_degree G K C x y v k hG hx hy ht htk hother hv hxD hdeg
  have hn := singleton_g1_strict_order G K C y v hy ht hother hv
  have hcard : Fintype.card (IdentificationVertex (boundaryCollapse G R v)) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hn
  have heq : (k - K.ncard + 3) + 1 = k - K.ncard + 4 := by omega
  have hd' : NonrootDegreeAtLeast (boundaryQuotient G R v) none
      (some (boundaryRetainedRoot G R v (by rw [singleton_g1_full_boundary G K C]; exact hv)))
      ((k - K.ncard + 3) + 1) := by
    rw [heq]
    exact hd
  exact ih (IdentificationVertex (boundaryCollapse G R v)) (boundaryQuotient G R v) none
    (some (boundaryRetainedRoot G R v (by rw [singleton_g1_full_boundary G K C]; exact hv)))
    (k - K.ncard + 3) hcard (by omega) hroot hd'

theorem singleton_g1_actual_family_transport [Fintype V] (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (x y v : V) (k : ℕ)
    (hK : G.IsClique K) (hx : x ∈ K) (hy : y ∉ K) (ht : 3 ≤ K.ncard)
    (htk : K.ncard ≤ k)
    (hother : C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩)
    (hv : v ∈ singletonG1Boundary G K C)
    (hxD : ¬∃ d : C.supp, G.Adj x d.1.1) (evy : G.Adj v y)
    (hchild : HasAdmissiblePaths (boundaryQuotient G (singletonG1Vertices G K C) v) none
      (some (boundaryRetainedRoot G (singletonG1Vertices G K C) v
        (by rw [singleton_g1_full_boundary G K C]; exact hv))) (k - K.ncard + 3)) :
    HasAdmissiblePaths G x y k := by
  classical
  let R := singletonG1Vertices G K C
  let S := equalBranchBoundary G R \ {v}
  let ell := k - K.ncard + 3
  have hvB : v ∈ equalBranchBoundary G R := by
    rw [singleton_g1_full_boundary G K C]
    exact hv
  have hxB : x ∉ singletonG1Boundary G K C := by
    rintro ⟨_hxK, d, edx⟩
    exact hxD ⟨d, edx.symm⟩
  have hxv : x ≠ v := fun he => hxB
    (Eq.mpr (congrArg (fun z : V => z ∈ singletonG1Boundary G K C) he) hv)
  have hyR : y ∉ R := by
    rintro ⟨hy', hyC⟩
    exact singleton_g1_point_ne_y G K y hy C hother ⟨⟨y, hy'⟩, hyC⟩ rfl
  have hyT : y ∉ boundaryDomain G R := by
    rintro (hyR' | hyB)
    · exact hyR hyR'
    · have hyB' : y ∈ singletonG1Boundary G K C := by
        rw [singleton_g1_full_boundary G K C] at hyB
        exact hyB
      exact hy hyB'.1
  obtain ⟨a, d, p, hp⟩ := hchild
  obtain ⟨s, q, hs, hfam, _hlen, hsupp⟩ :=
    identification_induced_family_lift G (boundaryDomain G R) S
      (boundaryRetainedRoot G R v hvB) ell a d p hp
  dsimp only [boundaryRetainedRoot] at q hfam
  have hsB : ∀ i : Fin ell, s i ∈ singletonG1Boundary G K C := by
    intro i
    have hh : s i ∈ equalBranchBoundary G R := (hs i).1
    rw [singleton_g1_full_boundary G K C] at hh
    exact hh
  have hsy : ∀ i : Fin ell, y ∉ (q i).support := by
    intro i hey
    exact hyT (hsupp i y hey).1
  have hqmeet : ∀ i z, z ∈ (q i).support → z ∈ evy.toWalk.support → z = v := by
    intro i z hz hzE
    rw [SimpleGraph.Adj.support_toWalk] at hzE
    have hzE' : z = v ∨ z = y := by simpa using hzE
    rcases hzE' with he | he
    · exact he
    · exact False.elim (hsy i (Eq.mp (congrArg (fun w : V => w ∈ (q i).support) he) hz))
  let L : ∀ i : Fin ell, G.Walk y (s i) := fun i => ((q i).append evy.toWalk).reverse
  have hL : ∀ i : Fin ell, (L i).IsPath := by
    intro i
    exact (append_isPath_of_only_common_endpoint (hfam.2.2 i).1 evy.isPath_toWalk (hqmeet i)).reverse
  have hLl : ∀ i : Fin ell, (L i).length = (a + 1) + i.val * d := by
    intro i
    change ((q i).append evy.toWalk).reverse.length = (a + 1) + i.val * d
    rw [Walk.length_reverse, Walk.length_append, evy.length_toWalk, (hfam.2.2 i).2]
    omega
  let F : Finset V := (Set.toFinite (K \ {v})).toFinset
  have hFset : (F : Set V) = K \ {v} := (Set.toFinite (K \ {v})).coe_toFinset
  have hFcard : F.card = K.ncard - 1 := by
    have hh : (K \ {v}).ncard = F.card := Set.ncard_eq_toFinset_card _ (Set.toFinite _)
    rw [← hh, Set.ncard_sdiff_singleton_of_mem hv.1]
  have hFcl : G.IsClique (F : Set V) := by
    rw [hFset]
    intro z hz w hw hzw
    exact hK hz.1 hw.1 hzw
  have hxF : x ∈ F := by
    change x ∈ (F : Set V)
    rw [hFset]
    exact ⟨hx, hxv⟩
  have hcEx : ∀ i : Fin ell, ∀ j : Fin (K.ncard - 2), ∃ c : G.Walk (s i) x,
      c.IsPath ∧ c.length = j.val + 1 ∧ ∀ z ∈ c.support, z ∈ F := by
    intro i j
    have hsF : s i ∈ F := by
      change s i ∈ (F : Set V)
      rw [hFset]
      exact ⟨(hsB i).1, (hs i).2⟩
    have hsx : s i ≠ x := fun he => hxB
      (Eq.mp (congrArg (fun z : V => z ∈ singletonG1Boundary G K C) he) (hsB i))
    have hj := j.isLt
    exact finset_clique_path_exact (j.val + 1) F (s i) x hFcl hsF hxF hsx
      (by omega) (by omega)
  choose c hc using hcEx
  have hqK : ∀ i z, z ∈ (q i).support → z ∈ F → z = s i := by
    intro i z hz hzF
    have hzK : z ∈ K \ {v} := by
      have hzF' : z ∈ (F : Set V) := hzF
      rw [hFset] at hzF'
      exact hzF'
    have hh := hsupp i z hz
    rcases hh.1 with hzR | hzB
    · obtain ⟨hzOut, _hzC⟩ := hzR
      exact False.elim (hzOut hzK.1)
    · rcases hh.2 with he | he
      · exact he
      · exact False.elim (he ⟨hzB, hzK.2⟩)
  have hmeet : ∀ i j z, z ∈ (L i).support → z ∈ (c i j).support → z = s i := by
    intro i j z hzL hzc
    have hzF := (hc i j).2.2 z hzc
    have hzA : z ∈ ((q i).append evy.toWalk).support := by
      simpa only [L, Walk.support_reverse, List.mem_reverse] using hzL
    rw [Walk.support_append] at hzA
    rcases List.mem_append.mp hzA with hzq | hzE
    · exact hqK i z hzq hzF
    · have hzE' : z ∈ evy.toWalk.support := List.mem_of_mem_tail hzE
      rw [SimpleGraph.Adj.support_toWalk] at hzE'
      have hzE'' : z = v ∨ z = y := by simpa using hzE'
      have hzK : z ∈ K \ {v} := by
        have hh : z ∈ (F : Set V) := hzF
        rw [hFset] at hh
        exact hh
      rcases hzE'' with he | he
      · exact False.elim (hzK.2 he)
      · exact False.elim (hy (Eq.mp (congrArg (fun w : V => w ∈ K) he) hzK.1))
  have hcl : ∀ i j, (c i j).length = 1 + j.val * 1 := by
    intro i j
    have hh := (hc i j).2.1
    omega
  have hyx := admissible_path_concatenation (G := G)
    (by dsimp [ell]; omega : 1 ≤ ell) (by omega : 1 ≤ K.ncard - 2)
    (by have ha := hfam.1; omega : 2 ≤ a + 1) (by omega : 1 ≤ (1 : ℕ))
    hfam.2.1 (Or.inl rfl) s L c hL (fun i j => (hc i j).1) hLl hcl hmeet
  have hcount : ell + (K.ncard - 2) - 1 = k := by dsimp [ell]; omega
  rw [hcount] at hyx
  obtain ⟨A, D, paths, hpaths⟩ := hyx
  exact ⟨A, D, (fun i => (paths i).reverse),
    (admissible_family_reverse G y x k A D paths hpaths).1⟩

theorem singleton_g1_branch_from_smaller_IH [Fintype V] (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (x y v : V) (k : ℕ)
    (hG : TwoConnected G) (hK : G.IsClique K) (hx : x ∈ K) (hy : y ∉ K)
    (ht : 3 ≤ K.ncard) (htk : K.ncard ≤ k)
    (hother : C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩)
    (hv : v ∈ singletonG1Boundary G K C)
    (hxD : ¬∃ d : C.supp, G.Adj x d.1.1) (evy : G.Adj v y)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) (s t : W) (ell : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ ell → RootedTwoConnected H s t →
        NonrootDegreeAtLeast H s t (ell + 1) → HasAdmissiblePaths H s t ell) :
    HasAdmissiblePaths G x y k := by
  have hchild := singleton_g1_family_from_smaller_IH G K C x y v k hG hx hy ht htk
    hother hv hxD hdeg ih
  exact singleton_g1_actual_family_transport G K C x y v k hK hx hy ht htk hother hv hxD evy hchild

#print axioms singleton_g1_family_from_smaller_IH
#print axioms singleton_g1_actual_family_transport
#print axioms singleton_g1_branch_from_smaller_IH
end TaskH.Gao
