import Research.TaskH.Gao.G6ActualTestTwoConnected
import Research.TaskH.Gao.G6DegreeAndOrder
import Research.TaskH.Gao.G6BicliquePathFamily
import Research.TaskH.Gao.BicliqueLexicographicSelection

/-! Complete conditional G6 branch under the original normalized casebi data.
The actual region, quotient degree, rooted connectivity, smaller order and
path families are conclusions, not supplied hypotheses. Matching and terminal
attachment conditions remain explicit local upstream obligations. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem g6_actual_nonroot_degree [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u w : V) (s k : ℕ)
    (hQ : CasebiBiclique G x y A B)
    (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hu : u ∈ A) (hw : w ∈ B) (hxw : x ≠ w)
    (hA : A.ncard = s + 1) (hB : B.ncard = s + 1)
    (hs : 2 ≤ s) (hsk : s + 2 ≤ k)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hS : (g6Boundary G (g6SelectedRegion G A B y w) A u).Nonempty)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast (g6Graph G (g6SelectedRegion G A B y w) A u w)
      (some (Sum.inr false)) none (k - s + 2) := by
  classical
  let H := g6SelectedRegion G A B y w
  let D : Set V := B \ ({x} : Set V)
  have hAB := hQ.1
  have hx : x ∈ B := hQ.2.2.1
  have hHA : Disjoint H A := Disjoint.mono_right Set.subset_union_left (g6Selected_disjoint_core G A B y w)
  have hwH : w ∉ H := fun h => (g6Selected_subset_outside G A B y w h).1 (Or.inr hw)
  have hwA : w ∉ A := fun h => Set.disjoint_left.mp hAB h hw
  have hwD : w ∈ D := ⟨hw, Ne.symm hxw⟩
  have hD : D.ncard = s := by
    have he := Set.ncard_sdiff_singleton_add_one hx
    change D.ncard + 1 = B.ncard at he
    omega
  have hcover := g6Selected_neighbor_cover_without_x G A B x y w hNx hNy
  have hloss : ∀ h : H, (G.neighborSet h.1).ncard -
      ((g6Graph G H A u w).neighborSet (some (Sum.inl h))).ncard ≤ s - 1 := by
    intro h
    have hc : G.neighborSet h.1 ⊆ H ∪ (A ∪ D) := by
      intro v e
      rcases hcover h.1 h.2 v e with hvH | hvA | hvD
      · exact Or.inl hvH
      · exact Or.inr (Or.inl hvA)
      · exact Or.inr (Or.inr hvD)
    by_cases htoA : ∃ a ∈ A, G.Adj h.1 a
    · by_cases htoD : ∃ b ∈ D, G.Adj h.1 b
      · have hv : h.1 ∉ (A ∪ B) ∪ {y} := by
          rintro (hAB | hy)
          · exact (g6Selected_subset_outside G A B y w h.2).1 hAB
          · exact (g6Selected_subset_outside G A B y w h.2).2 hy
        have hm := casebi_mixed_first_card G x y A B hQ htri hquad h.1 hv htoA
          (by obtain ⟨b, hb, eb⟩ := htoD; exact ⟨b, hb.1, eb⟩)
        have huniq : ∀ a ∈ A, ∀ b ∈ A, G.Adj h.1 a → G.Adj h.1 b → a = b := by
          intro a ha b hb ea eb
          exact (Set.ncard_le_one (Set.toFinite (G.neighborSet h.1 ∩ A))).mp
            (le_of_eq hm) a ⟨ea, ha⟩ b ⟨eb, hb⟩
        exact g6_h_mixed_unique_A_loss_bound G H A D u w s hu hHA hwH hwA hwD hD h hc huniq
      · have hcA : G.neighborSet h.1 ⊆ H ∪ A := by
          intro v e
          rcases hc e with hvH | hvA | hvD
          · exact Or.inl hvH
          · exact Or.inr hvA
          · exact False.elim (htoD ⟨v, hvD, e⟩)
        exact g6_h_A_only_loss_bound G H A u w s hu hHA hwH hwA hA h hcA
    · have hcD : G.neighborSet h.1 ⊆ H ∪ D := by
        intro v e
        rcases hc e with hvH | hvA | hvD
        · exact Or.inl hvH
        · exact False.elim (htoA ⟨v, hvA, e⟩)
        · exact Or.inr hvD
      exact g6_h_B_only_loss_bound G H A D u w s hu hHA hwH hwA hwD hD h hcD
  have hind := casebi_parts_independent G x y A B hQ htri hquad
  have hcoverW := g6_w_neighbor_cover G A B y w hw hind.2 hNy hAB
  intro p hpU hpT
  cases p with
  | none => exact False.elim (hpT rfl)
  | some p =>
    cases p with
    | inl h =>
      have hhx : h.1 ≠ x := by
        intro he
        have hhB : h.1 ∈ B := Eq.mpr (congrArg (fun z : V => z ∈ B) he) hx
        exact (g6Selected_subset_outside G A B y w h.2).1 (Or.inr hhB)
      have hhy : h.1 ≠ y := (g6Selected_subset_outside G A B y w h.2).2
      have hhdeg := hd h.1 hhx hhy
      have hhloss := hloss h
      change k - s + 2 ≤ ((g6Graph G H A u w).neighborSet (some (Sum.inl h))).ncard
      omega
    | inr b =>
      cases b with
      | false => exact False.elim (hpU rfl)
      | true =>
        have hwy : w ≠ y := by
          intro he
          exact hQ.2.2.2.1 (Or.inr (Eq.mp (congrArg (fun z : V => z ∈ B) he) hw))
        exact g6_w_degree_bound G H A u w s k hu hHA hwH hwA hA hS hcoverW
          (fun a ha => hQ.2.1 a ha w hw) hsk (hd w (Ne.symm hxw) hwy)

theorem g6_original_normalized_branch [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u w : V) (s k : ℕ)
    (hQ : CasebiBiclique G x y A B)
    (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hu : u ∈ A) (hw : w ∈ B) (hxw : x ≠ w)
    (hA : A.ncard = s + 1) (hB : B.ncard = s + 1)
    (hs : 2 ≤ s) (hsk : s + 2 ≤ k)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hH : (g6SelectedRegion G A B y w).Nonempty)
    (hM : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C → g6ComponentMatching G A B y C)
    (hAttach : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C →
      ∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
        ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  let H := g6SelectedRegion G A B y w
  let : Fintype (G6Vertex H) := g6ActualVertexFintype G A B y w
  have hHA : Disjoint H A := Disjoint.mono_right Set.subset_union_left (g6Selected_disjoint_core G A B y w)
  have hHB : Disjoint H B := Disjoint.mono_right Set.subset_union_right (g6Selected_disjoint_core G A B y w)
  have hHy : y ∉ H := fun hy => (g6Selected_subset_outside G A B y w hy).2 rfl
  have hwH : w ∉ H := fun h => Set.disjoint_left.mp hHB h hw
  have hwA : w ∉ A := fun h => Set.disjoint_left.mp hQ.1 h hw
  obtain ⟨v, hvH⟩ := hH
  obtain ⟨_hv, C, _hvC, t, htC, ewt⟩ :=
    (g6Selected_iff_actual_component G A B y w v).mp hvH
  have hC : g6ComponentTouches G A B y w C := ⟨⟨t, htC⟩, ewt⟩
  have hS := g6_component_matching_boundary_nonempty G A B y w u C hC (hM C hC)
  have hroot := g6_actual_rooted_twoConnected G A B y u w hu hw hQ.2.1
    ⟨v, hvH⟩ hM hAttach
  have horder := g6_strict_original_order H A w hHA hwH hwA (by omega : 3 ≤ A.ncard)
  have horder' : Fintype.card (G6Vertex H) < Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using horder
  have hdegree := g6_actual_nonroot_degree G A B x y u w s k hQ htri hquad hu hw hxw
    hA hB hs hsk hNx hNy hS hd
  have hdegree' : NonrootDegreeAtLeast (g6Graph G H A u w)
      (some (Sum.inr false)) none ((k - s + 1) + 1) := by
    change NonrootDegreeAtLeast (g6Graph G H A u w)
      (some (Sum.inr false)) none (k - s + 2)
    exact hdegree
  have hchild := ih (G6Vertex H) (g6Graph G H A u w)
    (some (Sum.inr false)) none (k - s + 1) horder' (by omega) hroot hdegree'
  exact g6_actual_family_from_quotient G H A B x y u w s k hQ.1 hHA hHB hHy hQ.2.1
    hQ.2.2.1 hQ.2.2.2.1 hu hw hxw hA hB (by omega) (by omega) hNy hchild

theorem g6_original_normalized_contradiction [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u w : V) (s k : ℕ)
    (hQ : CasebiBiclique G x y A B)
    (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hu : u ∈ A) (hw : w ∈ B) (hxw : x ≠ w)
    (hA : A.ncard = s + 1) (hB : B.ncard = s + 1)
    (hs : 2 ≤ s) (hsk : s + 2 ≤ k)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hH : (g6SelectedRegion G A B y w).Nonempty)
    (hM : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C → g6ComponentMatching G A B y C)
    (hAttach : ∀ C : (G.induce (g6Outside A B y)).ConnectedComponent,
      g6ComponentTouches G A B y w C →
      ∀ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b →
        ∃ d ∈ I, ∃ a ∈ A, G.Adj d.1.1 a)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) : False := by
  exact hno (g6_original_normalized_branch G A B x y u w s k hQ htri hquad hu hw hxw
    hA hB hs hsk hNx hNy hH hM hAttach hd ih)

#print axioms g6_actual_nonroot_degree
#print axioms g6_original_normalized_branch
#print axioms g6_original_normalized_contradiction
end TaskH.Gao
