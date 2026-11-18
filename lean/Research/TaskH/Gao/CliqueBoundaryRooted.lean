import Research.TaskH.Gao.RegionRootedBridge

/-! Real spokes are extracted from the actual boundary, or from actual deletion connectivity. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

attribute [local instance] regionIdentificationFintype

theorem interior_boundary_spoke [iV : Fintype V] (G : SimpleGraph V)
    (B S : Set V) (b x : V) (hG : @TwoConnected V iV G) (hb : b ∈ B)
    (hI : ∃ v ∈ B, v ≠ b) (hx : x ∉ B ∪ S)
    (hcover : ∀ v ∈ B, v ≠ b → ∀ t, G.Adj v t → t ∈ B ∨ t ∈ S) :
    ∃ w : B, w.1 ≠ b ∧ ∃ s ∈ S, G.Adj s w.1 := by
  classical
  by_contra hn
  have hxB : x ∉ B := fun hx' => hx (Or.inl hx')
  have hxb : x ≠ b := fun he => hxB (he.symm ▸ hb)
  have hclosed : ∀ v : {t : V // t ≠ b}, v.1 ∈ B →
      ∀ z : {t : V // t ≠ b}, (G.induce {t : V | t ≠ b}).Adj v z → z.1 ∈ B := by
    intro v hv z e
    rcases hcover v.1 hv v.2 z.1 e with hzB | hzS
    · exact hzB
    · exact False.elim (hn ⟨⟨v.1, hv⟩, ⟨v.2, ⟨z.1, hzS, e.symm⟩⟩⟩)
  have hwalk : ∀ {v z : {t : V // t ≠ b}},
      (G.induce {t : V | t ≠ b}).Walk v z → v.1 ∈ B → z.1 ∈ B := by
    intro v z p
    induction p with
    | nil => exact fun h => h
    | cons e _ ih =>
      intro hv
      exact ih (hclosed _ hv _ e)
  obtain ⟨v, hv, hvb⟩ := hI
  obtain ⟨p⟩ := (hG.2.2 b) ⟨v, hvb⟩ ⟨x, hxb⟩
  exact hxB (hwalk p hv)

theorem cliqueBoundary_real_spoke (G : SimpleGraph V) (B K : Set V) (x b : V)
    (hS : (cliqueBlockBoundary G B K x b).Nonempty) :
    ∃ w : B, w.1 ≠ b ∧ ∃ s ∈ cliqueBlockBoundary G B K x b, G.Adj s w.1 := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨w, hw, hwb, ews⟩ := hs.2.2
  exact ⟨⟨w, hw⟩, ⟨hwb, ⟨s, hs, ews.symm⟩⟩⟩

theorem cliqueBlock_quotient_rooted (G : SimpleGraph V) (B K : Set V) (x : V)
    (hBK : Disjoint B K) [iB : Fintype B] (b : B)
    [iO : Fintype {w : (B ∪ cliqueBlockBoundary G B K x b.1 : Set V) //
      w.1 ∉ cliqueBlockBoundary G B K x b.1}]
    (hB : @TwoConnected B iB (G.induce B))
    (hS : (cliqueBlockBoundary G B K x b.1).Nonempty) :
    RootedTwoConnected
      (V := IdentificationVertex
        {w : (B ∪ cliqueBlockBoundary G B K x b.1 : Set V) |
          w.1 ∈ cliqueBlockBoundary G B K x b.1})
      (regionIdentificationGraph G B (cliqueBlockBoundary G B K x b.1)) none
      (some (regionRetainedVertex B (cliqueBlockBoundary G B K x b.1)
        (cliqueBlock_boundary_disjoint G B K x b.1 hBK) b)) := by
  obtain ⟨w, hwb, hspoke⟩ := cliqueBoundary_real_spoke G B K x b.1 hS
  have hne : w ≠ b := fun he => hwb (congrArg Subtype.val he)
  exact regionIdentification_rooted_from_real_spoke G B (cliqueBlockBoundary G B K x b.1)
    (cliqueBlock_boundary_disjoint G B K x b.1 hBK) (iB := iB) (iO := iO)
    b w hB hspoke hne

#print axioms interior_boundary_spoke
#print axioms cliqueBoundary_real_spoke
#print axioms cliqueBlock_quotient_rooted
end TaskH.Gao
