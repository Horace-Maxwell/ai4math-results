import Research.TaskT.HellyFive.UpperTransferMaximal

namespace TaskT.HellyFive.UpperTransfer
open Set FiniteGeometry

/-- For every lattice polytope with at most five nonvertex lattice points, the
total number of its lattice points is at most the proposed bound plus five. -/
def PolyBound (n b : ℕ) : Prop :=
  ∀ V : Finset (Grid n),
    let P := poly V
    let X := {z : Grid n | embed z ∈ P ∧ embed z ∉ P.extremePoints ℝ}
    X.ncard ≤ 5 → (P.extremePoints ℝ).ncard + X.ncard ≤ b + 5

theorem countContacts {n b : ℕ} {ι : Type*} [Fintype ι] {box X : Finset (Grid n)}
    (hbox : ∀ z : Grid n, embed z ∈ poly box → z ∈ box)
    (hXB : X ⊆ box) (hfive : X.card = 5) (hbound : PolyBound n b)
    (A : ι → Finset (Grid n)) (hAc : ∀ i, ClosedIn box (A i))
    (hAX : ∀ z ∈ box, (∀ i, z ∈ A i) ↔ z ∈ X)
    (witness : ∀ i, ∃ z ∈ box, z ∉ X ∧ ∀ j, j ≠ i → z ∈ A j) :
    Fintype.card ι ≤ b := by
  classical
  obtain ⟨E, _, hiX, w, hw⟩ := maximalContacts A hAc hAX witness
  let W := Finset.univ.image w
  let V := X ∪ W
  have win (i : ι) : w i ∈ W := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have inj : Function.Injective w := by
    intro i j h
    by_contra hne
    exact (hw j).2.1 (h ▸ (hw i).2.2.1 j (Ne.symm hne))
  have xw : Disjoint X W := by
    apply Finset.disjoint_left.mpr
    intro z hz hwz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hwz
    exact (hw i).2.1 ((hiX _ (hw i).1).mpr hz i)
  have vb : V ⊆ box := by
    intro z hz
    rcases Finset.mem_union.mp hz with hx | h
    · exact hXB hx
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact (hw i).1
  have vsub (i : ι) : V ⊆ insert (w i) (E i) := by
    intro z hz
    apply Finset.mem_insert.mpr
    rcases Finset.mem_union.mp hz with hx | h
    · exact Or.inr ((hiX z (hXB hx)).mpr hx i)
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
      by_cases hh : j = i
      · exact Or.inl (congrArg w hh)
      · exact Or.inr ((hw j).2.2.1 i (Ne.symm hh))
  have grid (z : Grid n) : embed z ∈ poly V ↔ z ∈ V := by
    refine ⟨fun hz => ?_, poly_mem⟩
    by_cases hzw : z ∈ W
    · exact Finset.mem_union_right _ hzw
    have hzb := hbox z (poly_mono vb hz)
    apply Finset.mem_union_left
    apply (hiX z hzb).mp
    intro i
    have h := (hw i).2.2.2.1.2 z hzb (poly_mono (vsub i) hz)
    exact (Finset.mem_insert.mp h).resolve_left (fun x => hzw (x ▸ win i))
  have we (i : ι) : embed (w i) ∈ (poly V).extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset (poly_mono (vsub i))
      ⟨poly_mem (Finset.mem_union_right X (win i)),(hw i).2.2.2.2⟩
  let ex := V.filter fun z => embed z ∈ (poly V).extremePoints ℝ
  let nx := V.filter fun z => embed z ∉ (poly V).extremePoints ℝ
  have exid : (poly V).extremePoints ℝ = embed '' (ex : Set (Grid n)) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨z,hz,rfl⟩ := extremePoints_convexHull_subset hx
      exact ⟨z,Finset.mem_filter.mpr ⟨hz,hx⟩,rfl⟩
    · rintro _ ⟨z,hz,rfl⟩
      exact (Finset.mem_filter.mp hz).2
  have nxid : {z : Grid n | embed z ∈ poly V ∧ embed z ∉ (poly V).extremePoints ℝ} =
      (nx : Set _) := by
    ext z
    exact ⟨fun h => Finset.mem_filter.mpr ⟨(grid z).mp h.1,h.2⟩,
      fun h => ⟨(grid z).mpr (Finset.mem_filter.mp h).1,(Finset.mem_filter.mp h).2⟩⟩
  have nxsub : nx ⊆ X := by
    intro z hz
    obtain ⟨hz,hne⟩ := Finset.mem_filter.mp hz
    apply (Finset.mem_union.mp hz).resolve_right
    intro hzW
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hzW
    exact hne (we i)
  have cnt := hbound V
  simp only at cnt
  rw [nxid, exid, Set.ncard_image_of_injective _ embed_inj] at cnt
  simp only [Set.ncard_coe_finset] at cnt
  have h := cnt ((Finset.card_le_card nxsub).trans hfive.le)
  have split : ex.card + nx.card = V.card := Finset.card_filter_add_card_filter_not _
  have wc : W.card = Fintype.card ι := by simp [W, Finset.card_image_of_injective _ inj]
  have vc : V.card = X.card + W.card := Finset.card_union_of_disjoint xw
  omega

end TaskT.HellyFive.UpperTransfer
