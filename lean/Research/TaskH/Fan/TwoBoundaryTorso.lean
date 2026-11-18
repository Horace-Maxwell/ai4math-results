import Research.TaskH.Fan.TorsoRetraction

/-! A complete elementary two-boundary torso theorem with actual induced graphs. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem twoBoundaryTorso_retraction (A : SimpleGraph V) (S : Set V)
    (a b r : S) (hab : a ≠ b) (hr : r = a ∨ r = b)
    (hc : ∀ v ∈ S, v ≠ a.1 → v ≠ b.1 → ∀ w, A.Adj v w → w ∈ S) :
    ∀ {v w : V}, A.Adj v w →
      torsoRetraction S r v = torsoRetraction S r w ∨
        ((A.induce S) ⊔ SimpleGraph.edge a b).Adj
          (torsoRetraction S r v) (torsoRetraction S r w) := by
  classical
  let H := (A.induce S) ⊔ SimpleGraph.edge a b
  have hcross : ∀ v ∈ S, ∀ w ∉ S, A.Adj v w →
      torsoRetraction S r v = torsoRetraction S r w ∨
        H.Adj (torsoRetraction S r v) (torsoRetraction S r w) := by
    intro v hv w hw hvw
    have hvab : v = a.1 ∨ v = b.1 := by
      by_cases hva : v = a.1
      · exact Or.inl hva
      · right
        by_contra hvb
        exact hw (hc v hv hva hvb w hvw)
    have hvab' : (⟨v, hv⟩ : S) = a ∨ (⟨v, hv⟩ : S) = b :=
      hvab.imp Subtype.ext Subtype.ext
    rw [torsoRetraction_mem S r v hv, torsoRetraction_not_mem S r w hw]
    rcases hvab' with h | h <;> rcases hr with hr | hr
    · rw [h, hr]
      exact Or.inl rfl
    · rw [h, hr]
      exact Or.inr (Or.inr ((SimpleGraph.edge_adj a b a b).mpr
        ⟨Or.inl ⟨rfl, rfl⟩, hab⟩))
    · rw [h, hr]
      exact Or.inr (Or.inr ((SimpleGraph.edge_adj a b b a).mpr
        ⟨Or.inr ⟨rfl, rfl⟩, Ne.symm hab⟩))
    · rw [h, hr]
      exact Or.inl rfl
  intro v w hvw
  by_cases hv : v ∈ S
  · by_cases hw : w ∈ S
    · right
      rw [torsoRetraction_mem S r v hv, torsoRetraction_mem S r w hw]
      exact Or.inl hvw
    · exact hcross v hv w hw hvw
  · by_cases hw : w ∈ S
    · rcases hcross w hw v hv hvw.symm with he | he
      · exact Or.inl he.symm
      · exact Or.inr he.symm
    · left
      rw [torsoRetraction_not_mem S r v hv, torsoRetraction_not_mem S r w hw]

theorem twoBoundaryTorso_twoConnected [Fintype V] (A : SimpleGraph V)
    (S : Set V) [Fintype S] (a b : S) (hab : a ≠ b)
    (hcard : 3 ≤ Fintype.card S) (hA : TwoConnected A)
    (hc : ∀ v ∈ S, v ≠ a.1 → v ≠ b.1 → ∀ w, A.Adj v w → w ∈ S) :
    TwoConnected ((A.induce S) ⊔ SimpleGraph.edge a b) := by
  classical
  refine ⟨hcard, ?_, ?_⟩
  · exact torsoRetraction_connected A S _ a
      (twoBoundaryTorso_retraction A S a b a hab (Or.inl rfl) hc) hA.2.1
  · intro w
    by_cases hwa : w = a
    · have hwb : w ≠ b := by
        intro he
        exact hab (hwa.symm.trans he)
      exact torsoRetraction_delete_connected A S _ b w hwb
        (twoBoundaryTorso_retraction A S a b b hab (Or.inr rfl) hc) (hA.2.2 w.1)
    · exact torsoRetraction_delete_connected A S _ a w hwa
        (twoBoundaryTorso_retraction A S a b a hab (Or.inl rfl) hc) (hA.2.2 w.1)

#print axioms twoBoundaryTorso_retraction
#print axioms twoBoundaryTorso_twoConnected
end TaskH.Fan
