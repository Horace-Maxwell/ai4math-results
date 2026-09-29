import Research.Backfill.Paper4.Challenge

/-! A finite graph fingerprint and its invariance under actual graph isomorphisms.
The fingerprint is not claimed to classify all finite graphs. Its separate finite
evaluation on the 59 listed representatives is the required separation certificate.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4.TriangleFreeFingerprint

def vertexFingerprint {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : ℕ :=
  G.degree v + 8 * ∑ w ∈ G.neighborFinset v, 8 ^ G.degree w

def graphFingerprint {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Multiset ℕ :=
  (Finset.univ : Finset V).val.map (vertexFingerprint G)

theorem neighborFinset_map {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (v : V) :
    (G.neighborFinset v).map e.toEquiv.toEmbedding = H.neighborFinset (e v) := by
  classical
  ext w
  simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact e.map_adj_iff.mpr hu
  · intro hw
    refine ⟨e.symm w, ?_, ?_⟩
    · exact e.map_adj_iff.mp (by simpa only [RelIso.apply_symm_apply] using hw)
    · exact e.apply_symm_apply w

theorem vertexFingerprint_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (v : V) : vertexFingerprint H (e v) = vertexFingerprint G v := by
  have hs : (∑ w ∈ H.neighborFinset (e v), 8 ^ H.degree w) =
      ∑ w ∈ G.neighborFinset v, 8 ^ G.degree w := by
    rw [← neighborFinset_map e v, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro w _
    change 8 ^ H.degree (e w) = 8 ^ G.degree w
    rw [e.degree_eq]
  unfold vertexFingerprint
  rw [e.degree_eq, hs]

theorem graphFingerprint_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) : graphFingerprint H = graphFingerprint G := by
  unfold graphFingerprint
  rw [← Multiset.map_univ_val_equiv e.toEquiv, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro v _
  exact vertexFingerprint_iso e v

theorem not_iso_of_fingerprint_ne {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hne : graphFingerprint G ≠ graphFingerprint H) : ¬ Nonempty (G ≃g H) := by
  rintro ⟨e⟩
  exact hne (graphFingerprint_iso e).symm

#print axioms vertexFingerprint_iso
#print axioms graphFingerprint_iso

end CodexPaper4.TriangleFreeFingerprint
