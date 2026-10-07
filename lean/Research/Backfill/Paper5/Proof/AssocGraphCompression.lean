import Research.Backfill.Paper5.Supplement.AssociativityStatement

set_option autoImplicit false

universe u v

namespace CodexPaper5.AssocGraphCompression

/-- In an actual mapped graph, a path starting in the image stays in the image
and lifts to a path of the source graph. -/
theorem reachable_map_embedding_iff {V : Type u} {W : Type v}
    (f : V ↪ W) (G : SimpleGraph V) (p q : V) :
    (G.map f).Reachable (f p) (f q) ↔ G.Reachable p q := by
  constructor
  · intro h
    have hr := ((G.map f).reachable_iff_reflTransGen (f p) (f q)).mp h
    have hlift : ∀ {w : W}, Relation.ReflTransGen (G.map f).Adj (f p) w →
        ∃ r : V, f r = w ∧ G.Reachable p r := by
      intro w hw
      induction hw with
      | refl => exact ⟨p, rfl, SimpleGraph.Reachable.rfl⟩
      | @tail a b _ hab ih =>
        obtain ⟨r, hr, hpr⟩ := ih
        obtain ⟨s, t, hst, hs, ht⟩ := (SimpleGraph.map_adj f G a b).mp hab
        have hrs : r = s := f.injective (hr.trans hs.symm)
        have hrt : G.Adj r t := by
          rw [hrs]
          exact hst
        exact ⟨t, ht, hpr.trans hrt.reachable⟩
    obtain ⟨r, hr, hpr⟩ := hlift hr
    have hrq : r = q := f.injective hr
    rw [hrq] at hpr
    exact hpr
  · intro h
    exact h.map (SimpleGraph.Embedding.map f G).toHom

/-- Vertices outside the image of an actual mapped graph are isolated;
reachability from such a vertex is exactly equality, even for empty types. -/
theorem reachable_map_outside_iff {V : Type u} {W : Type v}
    (f : V ↪ W) (G : SimpleGraph V) (p q : W)
    (hp : ∀ a : V, f a ≠ p) :
    (G.map f).Reachable p q ↔ q = p := by
  constructor
  · intro h
    have hr := ((G.map f).reachable_iff_reflTransGen p q).mp h
    clear h
    induction hr with
    | refl => rfl
    | @tail _a b _ hab ih =>
      have hpb : (G.map f).Adj p b := by
        rw [← ih]
        exact hab
      obtain ⟨r, _s, _hrs, hr, _hs⟩ := (SimpleGraph.map_adj f G p b).mp hpb
      exact (hp r hr).elim
  · intro h
    subst q
    exact SimpleGraph.Reachable.rfl

/-- Replacing a graph by its full retained-pair connectivity preserves those
pairs after adjoining any additional graph supported on the retained image. -/
theorem reachable_sup_map_iff {V : Type u} {W : Type v}
    (f : W ↪ V) (G : SimpleGraph V) (C H : SimpleGraph W)
    (hboundary : ∀ p q : W, G.Reachable (f p) (f q) ↔ C.Reachable p q)
    (p q : W) :
    (G ⊔ H.map f).Reachable (f p) (f q) ↔ (C ⊔ H).Reachable p q := by
  constructor
  · intro h
    have hr := ((G ⊔ H.map f).reachable_iff_reflTransGen (f p) (f q)).mp h
    have hcompress : ∀ {w : V},
        Relation.ReflTransGen (G ⊔ H.map f).Adj (f p) w →
        ∃ r : W, (C ⊔ H).Reachable p r ∧ G.Reachable (f r) w := by
      intro w hw
      induction hw with
      | refl => exact ⟨p, SimpleGraph.Reachable.rfl, SimpleGraph.Reachable.rfl⟩
      | @tail a b _ hab ih =>
        obtain ⟨r, hpr, hra⟩ := ih
        rcases (SimpleGraph.sup_adj G (H.map f) a b).mp hab with hG | hH
        · exact ⟨r, hpr, hra.trans hG.reachable⟩
        · obtain ⟨s, t, hst, hs, ht⟩ := (SimpleGraph.map_adj f H a b).mp hH
          have hrs : G.Reachable (f r) (f s) := by
            rw [hs]
            exact hra
          have hcs : C.Reachable r s := (hboundary r s).mp hrs
          have hcs' : (C ⊔ H).Reachable r s := hcs.mono le_sup_left
          have hst' : (C ⊔ H).Reachable s t := hst.reachable.mono le_sup_right
          have htb : G.Reachable (f t) b := by
            rw [ht]
          exact ⟨t, hpr.trans (hcs'.trans hst'), htb⟩
    obtain ⟨r, hpr, hrq⟩ := hcompress hr
    exact hpr.trans (((hboundary r q).mp hrq).mono le_sup_left)
  · intro h
    have hr := ((C ⊔ H).reachable_iff_reflTransGen p q).mp h
    clear h
    have hlift : ∀ {s t : W}, (C ⊔ H).Adj s t →
        (G ⊔ H.map f).Reachable (f s) (f t) := by
      intro s t hst
      rcases (SimpleGraph.sup_adj C H s t).mp hst with hC | hH
      · exact ((hboundary s t).mpr hC.reachable).mono le_sup_left
      · have hm : (H.map f).Reachable (f s) (f t) :=
          hH.reachable.map (SimpleGraph.Embedding.map f H).toHom
        exact hm.mono le_sup_right
    induction hr with
    | refl => exact SimpleGraph.Reachable.rfl
    | tail _ hst ih => exact ih.trans (hlift hst)

theorem check_ReachableElimination :
    CodexPaper5.AssociativityStatement.ReachableElimination.{u, v} := by
  intro V W f G C H hboundary p q
  exact reachable_sup_map_iff f G C H hboundary p q

end CodexPaper5.AssocGraphCompression

#print axioms CodexPaper5.AssocGraphCompression.reachable_map_embedding_iff
#print axioms CodexPaper5.AssocGraphCompression.reachable_map_outside_iff
#print axioms CodexPaper5.AssocGraphCompression.reachable_sup_map_iff
#print axioms CodexPaper5.AssocGraphCompression.check_ReachableElimination
