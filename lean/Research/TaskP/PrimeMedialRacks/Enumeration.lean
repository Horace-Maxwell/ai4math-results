import Research.TaskP.PrimeMedialRacks.ClassCount

namespace TaskP.PrimeMedialRacks

open Challenge

/-- Surjectivity of the affine classification on all non-two-reductive medial rack tables. -/
def ClassifiedAt (p : ℕ) : Prop :=
  ∀ op : Operation (Fin p), IsRack op → Medial op → ¬ TwoReductive op →
    ∃ k : Parameter p, Isomorphic op (affine k.1)

variable {p : ℕ} [Fact p.Prime]

theorem affineTable_properties (k : Parameter p) :
    IsRack (affineTable k.1) ∧ Idempotent (affineTable k.1) ∧
    Medial (affineTable k.1) ∧ ¬ TwoReductive (affineTable k.1) := by
  have f := affineTable_iso k.1
  have g := iso_symm f
  exact ⟨iso_rack g (affine_isRack k.2.1), iso_idempotent g (affine_idempotent _),
    iso_medial g (affine_medial _), fun h => affine_nonreductive k.2.2 (iso_reductive f h)⟩

theorem rack_count_of_classification (h : ClassifiedAt p) :
    classCount p (fun op => IsRack op ∧ Medial op) =
      classCount p (fun op => IsRack op ∧ TwoReductive op) + (p - 2) := by
  let A := fun op : Operation (Fin p) => IsRack op ∧ Medial op
  let B := fun op : Operation (Fin p) => IsRack op ∧ TwoReductive op
  change classCount p A = classCount p B + (p - 2)
  rw [classCount_partition A B (fun _ hb => ⟨hb.1, reductive_medial hb.1 hb.2⟩)
    (fun _ _ iso hs => ⟨iso_rack iso hs.1, iso_reductive iso hs.2⟩)]
  congr 1
  apply count_affine_models
  · intro k
    obtain ⟨hr, _, hm, hn⟩ := affineTable_properties k
    exact ⟨⟨hr, hm⟩, fun hred => hn hred.2⟩
  · rintro t ⟨⟨hr, hm⟩, hn⟩
    exact h t hr hm (fun hred => hn ⟨hr, hred⟩)

theorem quandle_count_of_classification (h : ClassifiedAt p) :
    classCount p (fun op => IsRack op ∧ Idempotent op ∧ Medial op) =
      classCount p (fun op => IsRack op ∧ Idempotent op ∧ TwoReductive op) + (p - 2) := by
  let A := fun op : Operation (Fin p) => IsRack op ∧ Idempotent op ∧ Medial op
  let B := fun op : Operation (Fin p) => IsRack op ∧ Idempotent op ∧ TwoReductive op
  change classCount p A = classCount p B + (p - 2)
  rw [classCount_partition A B (fun _ hb => ⟨hb.1, hb.2.1, reductive_medial hb.1 hb.2.2⟩)
    (fun _ _ iso hs => ⟨iso_rack iso hs.1, iso_idempotent iso hs.2.1, iso_reductive iso hs.2.2⟩)]
  congr 1
  apply count_affine_models
  · intro k
    obtain ⟨hr, hi, hm, hn⟩ := affineTable_properties k
    exact ⟨⟨hr, hi, hm⟩, fun hred => hn hred.2.2⟩
  · rintro t ⟨⟨hr, hi, hm⟩, hn⟩
    exact h t hr hm (fun hred => hn ⟨hr, hi, hred⟩)

theorem idempotent_of_classification (h : ClassifiedAt p) (op : Operation (Fin p))
    (hr : IsRack op) (hm : Medial op) (hn : ¬ TwoReductive op) : Idempotent op := by
  obtain ⟨k, hk⟩ := h op hr hm hn
  exact iso_idempotent (iso_symm hk) (affine_idempotent k.1)

end TaskP.PrimeMedialRacks
