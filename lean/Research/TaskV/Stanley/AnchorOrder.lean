import Research.TaskV.Stanley.AnchorCutLabels
import Research.TaskV.Stanley.AnchorRecords

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

variable {V W L : Type*} [Fintype V] [Fintype W] [Fintype L]
variable {G : SimpleGraph V} {H : SimpleGraph W}

def branchCode (w : V → ℕ) (tag : L → V) (s : Finset V) : ℕ × Finset L := by
  classical exact (∑ x ∈ s, w x, univ.filter fun i => tag i ∈ s)

omit [Fintype V] in
@[simp] theorem branchCode_mass (w : V → ℕ) (tag : L → V) (s : Finset V) :
    (branchCode w tag s).1 = ∑ x ∈ s, w x := rfl

omit [Fintype V] in
@[simp] theorem branchCode_mark (w : V → ℕ) (tag : L → V) (s : Finset V) (i : L) :
    i ∈ (branchCode w tag s).2 ↔ tag i ∈ s := by classical simp [branchCode]

def cutsMeetMarks (G : SimpleGraph V) (tag : L → V) : Prop :=
  ∀ s, connectedCut G s → ∃ i, tag i ∈ s

omit [Fintype V] [Fintype W] in
private theorem matching_side {w : V → ℕ} {z : W → ℕ} {a : L → V} {b : L → W}
    (same : markedSplits G w a = markedSplits H z b) {s : Finset V} (hs : connectedCut G s) :
    ∃ t, connectedCut H t ∧ branchCode z b t = branchCode w a s := by
  classical
  have h : branchCode w a s ∈ markedSplits G w a :=
    ⟨s,hs,rfl,branchCode_mark w a s⟩
  rw [same] at h
  obtain ⟨t,ht,hm,hl⟩ := h
  refine ⟨t,ht,Prod.ext hm ?_⟩
  ext i
  exact (branchCode_mark z b t i).trans (hl i).symm

omit [Fintype V] [Fintype W] in
theorem transfer_cut_marks {w : V → ℕ} {z : W → ℕ} {a : L → V} {b : L → W}
    (same : markedSplits G w a = markedSplits H z b) (hits : cutsMeetMarks G a) :
    cutsMeetMarks H b := by
  intro t ht
  obtain ⟨s,hs,e⟩ := matching_side same.symm ht
  obtain ⟨i,hi⟩ := hits s hs
  have hc := (branchCode_mark w a s i).mpr hi
  rw [e] at hc
  exact ⟨i,(branchCode_mark z b t i).mp hc⟩

/-- The partial order of rooted records is read directly from the mass and the set of marks. -/
theorem record_subset_iff_code (tree : G.IsTree) (w : V → ℕ) (positive : ∀ x, 0 < w x)
    (tag : L → V) (r : L) (hits : cutsMeetMarks G tag)
    (s t : RootedRecords G (tag r)) :
    s.val ⊆ t.val ↔ (branchCode w tag s.val).1 ≤ (branchCode w tag t.val).1 ∧
      (branchCode w tag s.val).2 ⊆ (branchCode w tag t.val).2 := by
  classical
  constructor
  · intro sub
    exact ⟨sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => Nat.zero_le (w i)),
      fun i hi => (branchCode_mark ..).mpr (sub ((branchCode_mark w tag s.val i).mp hi))⟩
  · rintro ⟨mass,marks⟩
    have mark : ∃ i, tag i ∈ s.val := by
      rcases s.property with h | h
      · exact ⟨r,h ▸ mem_univ _⟩
      · exact hits _ h.1
    obtain ⟨i,hi⟩ := mark
    have hj := (branchCode_mark w tag t.val i).mp (marks ((branchCode_mark w tag s.val i).mpr hi))
    have nested : s.val ⊆ t.val ∨ t.val ⊆ s.val := by
      rcases s.property with h | h
      · exact Or.inr (h ▸ subset_univ _)
      rcases t.property with g | g
      · exact Or.inl (g ▸ subset_univ _)
      exact tree_cut_laminar (s:=(s.val : Set V)) (t:=(t.val : Set V)) tree.isAcyclic
        h.1.1.preconnected h.1.2.preconnected g.1.1.preconnected g.1.2.preconnected
        h.2 g.2 hi hj
    rcases nested with sub | rev
    · exact sub
    · intro x hx
      by_contra hn
      exact (not_lt_of_ge mass) (sum_lt_sum_of_subset rev hx hn (positive x)
        (fun j _ _ => Nat.zero_le (w j)))

private theorem branchCode_injective (tree : G.IsTree) (w : V → ℕ) (positive : ∀ x, 0 < w x)
    (tag : L → V) (r : L) (hits : cutsMeetMarks G tag) :
    Function.Injective (fun s : RootedRecords G (tag r) => branchCode w tag s.val) := by
  intro s t h
  apply Subtype.ext
  apply Subset.antisymm
  · apply (record_subset_iff_code tree w positive tag r hits s t).mpr
    rw [show branchCode w tag s.val = branchCode w tag t.val from h]
    exact ⟨le_rfl,Subset.rfl⟩
  · apply (record_subset_iff_code tree w positive tag r hits t s).mpr
    rw [show branchCode w tag s.val = branchCode w tag t.val from h]
    exact ⟨le_rfl,Subset.rfl⟩

private theorem matching_record {w : V → ℕ} {z : W → ℕ} {a : L → V} {b : L → W}
    (same : markedSplits G w a = markedSplits H z b) (total : ∑ x, w x = ∑ y, z y)
    (r : L) (s : RootedRecords G (a r)) :
    ∃ t : RootedRecords H (b r), branchCode z b t.val = branchCode w a s.val := by
  classical
  rcases s.property with h | h
  · refine ⟨⟨univ,Or.inl rfl⟩,?_⟩
    rw [h]
    apply Prod.ext total.symm
    ext i
    simp
  · obtain ⟨t,ct,e⟩ := matching_side same h.1
    refine ⟨⟨t,Or.inr ⟨ct,?_⟩⟩,e⟩
    intro hr
    have mem := (branchCode_mark z b t r).mpr hr
    rw [e] at mem
    exact h.2 ((branchCode_mark w a s.val r).mp mem)

theorem matching_record_order (tg : G.IsTree) (th : H.IsTree)
    (w : V → ℕ) (z : W → ℕ) (pw : ∀ x, 0 < w x) (pz : ∀ y, 0 < z y)
    (a : L → V) (b : L → W) (r : L) (hits : cutsMeetMarks G a)
    (same : markedSplits G w a = markedSplits H z b) (total : ∑ x, w x = ∑ y, z y) :
    ∃ e : RootedRecords G (a r) ≃ RootedRecords H (b r),
      (∀ s, branchCode z b (e s).val = branchCode w a s.val) ∧
      ∀ s t, s.val ⊆ t.val ↔ (e s).val ⊆ (e t).val := by
  classical
  have hh := transfer_cut_marks same hits
  choose f hf using matching_record same total r
  have gi := branchCode_injective tg w pw a r hits
  have hi := branchCode_injective th z pz b r hh
  have inj : Function.Injective f := fun s t e => gi ((hf s).symm.trans (e ▸ hf t))
  have sur : Function.Surjective f := by
    intro t
    obtain ⟨s,hs⟩ := matching_record same.symm total.symm r t
    exact ⟨s,hi ((hf s).trans hs)⟩
  refine ⟨Equiv.ofBijective f ⟨inj,sur⟩,hf,?_⟩
  intro s t
  change s.val ⊆ t.val ↔ (f s).val ⊆ (f t).val
  rw [record_subset_iff_code tg w pw a r hits,record_subset_iff_code th z pz b r hh,hf s,hf t]

end
end StanleyContinuation
