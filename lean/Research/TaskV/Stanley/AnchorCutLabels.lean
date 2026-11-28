import Research.TaskV.Stanley.CoreWeights
import Research.TaskV.Stanley.StarSplit

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

/-- Each cut side records its total mass and the labels on that side. -/
def markedSplits {V L : Type*} (G : SimpleGraph V) (weight : V → ℕ) (label : L → V) :
    Set (ℕ × Finset L) :=
  {p | ∃ s : Finset V, connectedCut G s ∧ (∑ v ∈ s, weight v) = p.1 ∧
    ∀ i, i ∈ p.2 ↔ label i ∈ s}

private theorem decode_across {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    {A : Finset (Fin n)}
    (decode : ∀ P Q : Finset (Fin n), P ⊆ core G → Q ⊆ core G →
      (∑ v ∈ P, coreWeight G v) = (∑ v ∈ Q, coreWeight G v) →
      ∀ a ∈ A, (a ∈ P ↔ a ∈ Q))
    (e : ↥(core G) ≃ ↥(core H)) (weight : ∀ v, coreWeight H (e v) = coreWeight G v)
    {s : Finset ↥(core G)} {t : Finset ↥(core H)}
    (mass : (∑ v ∈ s, coreWeight G v) = ∑ v ∈ t, coreWeight H v)
    (a : ↥(core G)) (ha : a.val ∈ A) : a ∈ s ↔ e a ∈ t := by
  classical
  let emb := Function.Embedding.subtype (fun x => x ∈ core G)
  let u := t.map e.symm.toEmbedding
  have equal : (∑ v ∈ s.map emb, coreWeight G v) = ∑ v ∈ u.map emb, coreWeight G v := by
    simpa only [Finset.sum_map, emb, Function.Embedding.coe_subtype, u,
      Equiv.coe_toEmbedding, ← weight, Equiv.apply_symm_apply] using mass
  have inside (v : Finset ↥(core G)) : v.map emb ⊆ core G :=
    fun _ h => v.property_of_mem_map_subtype h
  have hx := decode _ _ (inside s) (inside u) equal a.val ha
  change emb a ∈ s.map emb ↔ emb a ∈ u.map emb at hx
  simpa only [Finset.mem_map', u, Finset.mem_map_equiv, Equiv.symm_symm] using hx

/-- Both trees give exactly the same set of side masses and anchor incidences, from ordinary X.
The competitors are arbitrary finite trees. No adjacency preservation of the core bijection is assumed. -/
theorem anchorCutProfiles_of_sameCSF {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (hG : G.IsTree) (hH : H.IsTree) (anchors : DecodableLeafAnchors G) (same : SameCSF G H) :
    ∃ (A : Finset (Fin n)) (incl : A ⊆ core G) (e : ↥(core G) ≃ ↥(core H)),
      (∀ a ∈ A, ∀ v ∈ core G, coreWeight G v = coreWeight G a → v = a) ∧
      (∀ v ∈ core G, ((neighbors G v) ∩ core G).card = 1 → v ∈ A) ∧
      (∀ v, coreWeight H (e v) = coreWeight G v) ∧
      markedSplits (coreGraph G) (fun v => coreWeight G v)
        (fun a : ↥A => (⟨a.val,incl a.property⟩ : ↥(core G))) =
      markedSplits (coreGraph H) (fun v => coreWeight H v)
        (fun a : ↥A => e ⟨a.val,incl a.property⟩) := by
  classical
  obtain ⟨hc,proper,A,incl,unique,cover,decode⟩ := anchors
  have hn : 2 ≤ n := hc.trans (by simpa only [Fintype.card_fin] using card_le_univ (core G))
  obtain ⟨e,weight⟩ := coreWeights_of_sameCSF hG hH hn proper same
  have cg := card_pos.mp (by omega : 0 < (core G).card)
  obtain ⟨v,hv⟩ := cg
  have ch : (core H).Nonempty := ⟨(e ⟨v,hv⟩).val,(e ⟨v,hv⟩).property⟩
  have ph (w : Fin m) (hw : w ∈ core H) : 2 ≤ coreWeight H w := by
    obtain ⟨a,ea⟩ := e.surjective (⟨w,hw⟩ : ↥(core H))
    have eq := weight a
    rw [ea] at eq
    exact (proper _ a.property).trans_eq eq.symm
  let tag (a : ↥A) : ↥(core G) := ⟨a.val,incl a.property⟩
  have labels {s : Finset ↥(core G)} {t : Finset ↥(core H)}
      (hm : (∑ v ∈ s, coreWeight G v) = ∑ v ∈ t, coreWeight H v) (a : ↥A) :
      tag a ∈ s ↔ e (tag a) ∈ t := decode_across decode e weight hm (tag a) a.property
  refine ⟨A,incl,e,unique,cover,weight,?_⟩
  ext p
  have conn := sameConnected_of_sameCSF hG hH same
  have size := sameOrder_of_sameCSF same
  constructor
  · rintro ⟨s,cs,sm,sl⟩
    obtain ⟨t,ct,hm⟩ := matching_core_cut hG.connected hH.connected ⟨v,hv⟩ ch conn size proper s cs
    exact ⟨t,ct,hm.trans sm,fun a => (sl a).trans (labels hm.symm a)⟩
  · rintro ⟨t,ct,tm,tl⟩
    obtain ⟨s,cs,hm⟩ := matching_core_cut hH.connected hG.connected ch ⟨v,hv⟩
      (fun k z => (conn k z).symm) size.symm ph t ct
    exact ⟨s,cs,hm.trans tm,fun a => (tl a).trans (labels hm a).symm⟩

end
end StanleyContinuation
