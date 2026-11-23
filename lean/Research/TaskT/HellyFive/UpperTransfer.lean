import Research.TaskT.HellyFive.UpperTransferCount

namespace TaskT.HellyFive
open Set FiniteGeometry UpperTransfer

/-- The upper implication of the polytopal description for five common lattice
points. No closedness, boundedness, or full dimension of the original sets is assumed. -/
theorem preservesFive_of_polyBound {n b : ℕ} (hbound : PolyBound n b) :
    PreservesFive n b := by
  classical
  intro m _ C cv h5
  let G := commonGrid C Finset.univ
  change G.encard = 5 at h5
  have hfin : G.Finite := Set.finite_of_encard_eq_coe (k := 5) h5
  let X := hfin.toFinset
  have hx (z : Grid n) : z ∈ X ↔ z ∈ G := hfin.mem_toFinset
  have hcard : X.card = 5 := by
    exact_mod_cast hfin.encard_eq_coe_toFinset_card.symm.trans h5
  let opts := (Finset.univ : Finset (Fin m)).powerset.filter fun s => commonGrid C s = G
  have start : Finset.univ ∈ opts := Finset.mem_filter.mpr ⟨Finset.mem_powerset_self _,rfl⟩
  obtain ⟨I,hI,hmin⟩ := opts.exists_min_image Finset.card ⟨_,start⟩
  have hi : commonGrid C I = G := (Finset.mem_filter.mp hI).2
  refine ⟨I, ?_, hi ▸ h5⟩
  have indispensable (i : I) : ∃ z : Grid n, z ∉ X ∧
      ∀ j : I, j ≠ i → embed z ∈ C j.val := by
    have hn : ¬commonGrid C (I.erase i.val) ⊆ G := by
      intro small
      have eq : commonGrid C (I.erase i.val) = G :=
        small.antisymm (fun _ hG j _ => hG j (Finset.mem_univ _))
      have h := hmin (I.erase i.val) (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),eq⟩)
      exact (Finset.card_erase_lt_of_mem i.property).not_ge h
    obtain ⟨z,hz,hnot⟩ := Set.not_subset.mp hn
    exact ⟨z,fun h => hnot ((hx z).mp h), fun j hji =>
      hz j.val (Finset.mem_erase.mpr ⟨fun heq => hji (Subtype.ext heq),j.property⟩)⟩
  choose w hwX hwC using indispensable
  let V := X ∪ Finset.univ.image w
  let box := (grid_poly_finite V).toFinset
  have hb (z : Grid n) : z ∈ box ↔ embed z ∈ poly V := (grid_poly_finite V).mem_toFinset
  have hvb : V ⊆ box := fun z hz => (hb z).mpr (poly_mem hz)
  have hXB : X ⊆ box := Finset.subset_union_left.trans hvb
  have hwb (i : I) : w i ∈ box :=
    hvb (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have closedBox (z : Grid n) (hz : embed z ∈ poly box) : z ∈ box := by
    apply (hb z).mpr
    refine convexHull_min ?_ (convex_convexHull ℝ _) hz
    rintro _ ⟨q,hq,rfl⟩
    exact (hb q).mp hq
  let A (i : I) := box.filter fun z => embed z ∈ C i.val
  have closedA (i : I) : ClosedIn box (A i) := by
    refine ⟨Finset.filter_subset .., fun z hzb hzp => Finset.mem_filter.mpr ⟨hzb,?_⟩⟩
    refine convexHull_min ?_ (cv i.val) hzp
    rintro _ ⟨q,hq,rfl⟩
    exact (Finset.mem_filter.mp hq).2
  have allA (z : Grid n) (hz : z ∈ box) : (∀ i : I, z ∈ A i) ↔ z ∈ X := by
    refine ⟨fun hall => (hx z).mpr (hi ▸ ?_), fun h i => ?_⟩
    · intro j hj
      exact (Finset.mem_filter.mp (hall ⟨j,hj⟩)).2
    · exact Finset.mem_filter.mpr ⟨hz, (hx z).mp h i.val (Finset.mem_univ _)⟩
  have witness (i : I) : ∃ z ∈ box, z ∉ X ∧ ∀ j : I, j ≠ i → z ∈ A j :=
    ⟨w i, hwb i, hwX i, fun j hji => Finset.mem_filter.mpr ⟨hwb i, hwC i j hji⟩⟩
  simpa using countContacts closedBox hXB hcard hbound A closedA allA witness

end TaskT.HellyFive
