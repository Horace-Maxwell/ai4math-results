import Research.Backfill.Paper7.SunDegrees

set_option autoImplicit false

noncomputable section

namespace Paper7Setup

open SimpleGraph BackfillPaper7.Challenge
open scoped Classical

theorem pq_get_short (b : ℕ) (p q : Fin b → ℕ) (k : Fin b)
    (j : Fin (pq b p q k).length) (hj : j.val < p k) : (pq b p q k).get j = 1 := by
  change (List.replicate (p k) 1 ++ List.replicate (q k) 2)[j.val] = 1
  rw [List.getElem_append_left (by simpa only [List.length_replicate] using hj)]
  simp only [List.getElem_replicate]

#print axioms Paper7Setup.pq_get_short

theorem pq_get_long (b : ℕ) (p q : Fin b → ℕ) (k : Fin b)
    (j : Fin (pq b p q k).length) (hj : p k ≤ j.val) : (pq b p q k).get j = 2 := by
  change (List.replicate (p k) 1 ++ List.replicate (q k) 2)[j.val] = 2
  rw [List.getElem_append_right (by simpa only [List.length_replicate] using hj)]
  simp only [List.getElem_replicate]

#print axioms Paper7Setup.pq_get_long

/-- Short arms are exactly the neighbors of a root that have degree one.
In particular, this recovers p even when all arm counts are zero. -/
theorem sg_leaf_neighbor_card (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) (k : Fin b) :
    Fintype.card {v : (SG b p q).neighborSet (Sum.inl k) //
      (SG b p q).degree v.val = 1} = p k := by
  let idx : Fin (p k) → Fin (pq b p q k).length :=
    fun i => ⟨i.val, by rw [pq_length]; have := i.isLt; omega⟩
  have hi (i : Fin (p k)) : (pq b p q k).get (idx i) = 1 :=
    pq_get_short b p q k (idx i) i.isLt
  let f : Fin (p k) → {v : (SG b p q).neighborSet (Sum.inl k) //
      (SG b p q).degree v.val = 1} := fun i =>
    ⟨⟨Sum.inr ⟨k, idx i, ⟨0, by rw [hi]; decide⟩⟩,
      (Paper7Cleared.sun_root_arm_adj_iff b (pq b p q) k k (idx i) _).mpr ⟨rfl, rfl⟩⟩,
      sun_arm_degree_one k (idx i) (hi i) _⟩
  have hfinj : Function.Injective f := by
    intro i j heq
    apply Fin.ext
    exact congrArg (fun v : {v : (SG b p q).neighborSet (Sum.inl k) //
        (SG b p q).degree v.val = 1} =>
      match v.val.val with
      | Sum.inl _ => 0
      | Sum.inr z => z.2.1.val) heq
  have hfsurj : Function.Surjective f := by
    intro v
    rcases v with ⟨⟨x, hx⟩, hd⟩
    cases x with
    | inl i =>
      have hdeg := sg_root_degree b p q hb i
      change (SG b p q).degree (Sum.inl i) = 1 at hd
      omega
    | inr z =>
      rcases z with ⟨k', j, a⟩
      obtain ⟨hk, ha⟩ :=
        (Paper7Cleared.sun_root_arm_adj_iff b (pq b p q) k k' j a).mp hx
      subst k'
      have hj : j.val < p k := by
        by_contra hnot
        have hget : (pq b p q k).get j = 2 := pq_get_long b p q k j (by omega)
        have haz : a = ⟨0, by omega⟩ := Fin.ext ha
        have hdeg : (SG b p q).degree (Sum.inr ⟨k, j, a⟩) = 2 := by
          rw [haz]
          exact sun_arm_degree_two_first k j hget
        change (SG b p q).degree (Sum.inr ⟨k, j, a⟩) = 1 at hd
        omega
      refine ⟨⟨j.val, hj⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      dsimp only [f]
      exact Paper7SunMoments.sun_arm_vertex_eq_of_coords rfl rfl ha.symm
  calc
    Fintype.card {v : (SG b p q).neighborSet (Sum.inl k) //
      (SG b p q).degree v.val = 1} = Fintype.card (Fin (p k)) :=
      (Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)).symm
    _ = p k := Fintype.card_fin (p k)

#print axioms Paper7Setup.sg_leaf_neighbor_card

theorem leaf_neighbor_card_iso {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (G' : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (e : G ≃g G') (u : V) :
    Fintype.card {v : G.neighborSet u // G.degree v.val = 1} =
      Fintype.card {v : G'.neighborSet (e u) // G'.degree v.val = 1} := by
  apply Fintype.card_congr
  refine (e.mapNeighborSet u).subtypeEquiv ?_
  intro v
  change G.degree v.val = 1 ↔ G'.degree (e v.val) = 1
  rw [e.degree_eq]

#print axioms Paper7Setup.leaf_neighbor_card_iso

end Paper7Setup
