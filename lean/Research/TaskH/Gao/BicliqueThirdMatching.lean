import Research.TaskH.Gao.BicliqueThirdOriginalFamily
import Research.TaskH.Gao.BicliqueSingletonFirstFamily
import Research.TaskH.Gao.BicliqueSingletonSecondFamily
import Research.TaskH.Gao.G6ComponentAttachment

/-! Native component dichotomy and explicit transport to the original G6 predicate. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem biclique_no_native_matching_unique_side (G : SimpleGraph V) (A B : Set V)
    (y : V) (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hnonempty : ∃ d : C.supp, ∃ a ∈ A, G.Adj d.1.1 a)
    (hno : ¬∃ d e : C.supp, ∃ a b : V,
      a ∈ A ∧ b ∈ A ∧ d ≠ e ∧ a ≠ b ∧ G.Adj d.1.1 a ∧ G.Adj e.1.1 b) :
    (∃ a ∈ A, (∃ d : C.supp, G.Adj d.1.1 a) ∧
      ∀ (d : C.supp) b, b ∈ A → G.Adj d.1.1 b → b = a) ∨
    (∃ d : C.supp, (∃ a ∈ A, G.Adj d.1.1 a) ∧
      ∀ (e : C.supp) b, b ∈ A → G.Adj e.1.1 b → e = d) := by
  classical
  obtain ⟨d₀, a₀, ha₀, e₀⟩ := hnonempty
  by_cases hall : ∀ (d : C.supp) (a : V), a ∈ A → G.Adj d.1.1 a → a = a₀
  · exact Or.inl ⟨a₀, ha₀, ⟨d₀, e₀⟩, hall⟩
  · push Not at hall
    obtain ⟨d₁, a₁, ha₁, e₁, hne⟩ := hall
    have hd : d₁ = d₀ := by
      by_contra hdn
      exact hno ⟨d₁, d₀, a₁, a₀, ha₁, ha₀, hdn, hne, e₁, e₀⟩
    have e₁' : G.Adj d₀.1.1 a₁ :=
      Eq.mp (congrArg (fun d : C.supp => G.Adj d.1.1 a₁) hd) e₁
    refine Or.inr ⟨d₀, ⟨a₀, ha₀, e₀⟩, ?_⟩
    intro d a ha e
    by_contra hdn
    have haeq : a = a₀ := by
      by_contra han
      exact hno ⟨d, d₀, a, a₀, ha, ha₀, hdn, han, e, e₀⟩
    apply hno
    refine ⟨d, d₀, a, a₁, ha, ha₁, hdn, ?_, e, e₁'⟩
    intro he
    exact hne (he.symm.trans haeq)

theorem biclique_third_native_matching [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ (A ∪ B)).ncard ≤ s + 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) :
    ∃ d e : C.supp, ∃ a b : V,
      a ∈ A ∧ b ∈ A ∧ d ≠ e ∧ a ≠ b ∧ G.Adj d.1.1 a ∧ G.Adj e.1.1 b := by
  classical
  have hcapA : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ A).ncard ≤ s + 1 := by
    intro d
    have hsub : G.neighborSet d.1.1 ∩ A ⊆ G.neighborSet d.1.1 ∩ (A ∪ B) := by
      intro z hz
      exact ⟨hz.1, Or.inl hz.2⟩
    exact (Set.ncard_le_ncard hsub).trans (hcap d)
  have hAtouch := biclique_singleton_first_boundary G A B x y s k C hG hAB hc hx hy hs hsk
    hA hB hNx hNy hd ih hno
  have hBt := biclique_singleton_second_boundary G A B x y s k C hG hAB hc hx hy hs hsk
    hA hB hNx hNy hcapA hd ih hno
  have hBtouch : (bicliqueThirdCollapse G A B x y C).Nonempty := by
    obtain ⟨b, hb, d, ebd⟩ := hBt
    exact ⟨b, hb, d, ebd.symm⟩
  have hAe : ∃ d : C.supp, ∃ a ∈ A, G.Adj d.1.1 a := by
    obtain ⟨a, ha, d, ead⟩ := hAtouch
    exact ⟨d, a, ha, ead.symm⟩
  by_contra hnomatch
  rcases biclique_no_native_matching_unique_side G A B y C hAe hnomatch with
    ⟨a, ha, hda, hunique⟩ | ⟨d, ⟨w, hw, edw⟩, hunique⟩
  · have hcase : BicliqueThirdRootCase G A B y a C := Or.inl ⟨ha, hda, hunique⟩
    exact hno (biclique_third_original_family G A B x y a a s k C hG hAB hc hx hy ha hs hsk
      hA hB hNx hNy hcap hd hcase hBtouch (Or.inl rfl) ih)
  · have hdR : d.1.1 ∈ singletonG1Vertices G (bicliqueSingletonCore A B y) C :=
      ⟨d.1.2, d.2⟩
    have hcase : BicliqueThirdRootCase G A B y d.1.1 C := by
      right
      refine ⟨hdR, ?_⟩
      intro e a ha eea
      exact congrArg (fun z : C.supp => z.1.1) (hunique e a ha eea)
    exact hno (biclique_third_original_family G A B x y d.1.1 w s k C hG hAB hc hx hy hw hs hsk
      hA hB hNx hNy hcap hd hcase hBtouch (Or.inr ⟨hdR, edw⟩) ih)

def componentSetTransport (G : SimpleGraph V) {U W : Set V} (h : U = W)
    (C : (G.induce U).ConnectedComponent) : (G.induce W).ConnectedComponent :=
  Eq.mp (congrArg (fun T : Set V => (G.induce T).ConnectedComponent) h) C

theorem component_matching_set_transport (G : SimpleGraph V) (A : Set V)
    {U W : Set V} (h : U = W) (C : (G.induce U).ConnectedComponent) :
    (∃ d e : C.supp, ∃ a b : V,
      a ∈ A ∧ b ∈ A ∧ d ≠ e ∧ a ≠ b ∧ G.Adj d.1.1 a ∧ G.Adj e.1.1 b) ↔
    (∃ d e : (componentSetTransport G h C).supp, ∃ a b : V,
      a ∈ A ∧ b ∈ A ∧ d ≠ e ∧ a ≠ b ∧ G.Adj d.1.1 a ∧ G.Adj e.1.1 b) := by
  cases h
  exact Iff.rfl

theorem biclique_core_compl_eq_g6Outside (A B : Set V) (y : V) :
    (bicliqueSingletonCore A B y)ᶜ = g6Outside A B y := by
  ext z
  change (¬(z ∈ A ∪ B ∨ z = y)) ↔ (z ∉ A ∪ B ∧ z ≠ y)
  exact not_or

theorem biclique_singleton_actual_g6_matching [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hA : s + 1 ≤ A.ncard) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ (A ∪ B)).ncard ≤ s + 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hno : ¬HasAdmissiblePaths G x y k) :
    g6ComponentMatching G A B y
      (componentSetTransport G (biclique_core_compl_eq_g6Outside A B y) C) := by
  exact (component_matching_set_transport G A (biclique_core_compl_eq_g6Outside A B y) C).mp
    (biclique_third_native_matching G A B x y s k C hG hAB hc hx hy hs hsk hA hB hNx hNy hcap hd ih hno)

#print axioms biclique_no_native_matching_unique_side
#print axioms biclique_third_native_matching
#print axioms componentSetTransport
#print axioms component_matching_set_transport
#print axioms biclique_core_compl_eq_g6Outside
#print axioms biclique_singleton_actual_g6_matching
end TaskH.Gao
