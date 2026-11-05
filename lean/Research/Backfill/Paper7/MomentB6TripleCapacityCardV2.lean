import Research.Backfill.Paper7.MomentB6TripleDiscriminantKernel

/-! UNCOMPILED candidate by /root/moment_b6_labelled_symbolic_2310.
Full ordered capacity-triple cardinality bridge and its Q=0 kernel specialization.
The two imported local candidate modules are uncompiled parents, not successful
dependencies. No finite candidate enumeration is evaluated. The six displayed
position permutations are symbolic and their duplicates are removed by Finset.
No statement assumes a coverage, multiplicity, or cardinality conclusion. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

def labelledTripleOrbit (c a b : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  {(c, a, b), (c, b, a), (a, c, b), (a, b, c), (b, c, a), (b, a, c)}
#print axioms Paper7MomentCounts.labelledTripleOrbit

theorem labelledTripleOrbit_statistics (c a b : ℕ) (u : ℕ × ℕ × ℕ)
    (hu : u ∈ labelledTripleOrbit c a b) :
    u.1 + u.2.1 + u.2.2 = c + a + b ∧
      u.1^2 + u.2.1^2 + u.2.2^2 = c^2 + a^2 + b^2 := by
  simp only [labelledTripleOrbit, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> ring
#print axioms Paper7MomentCounts.labelledTripleOrbit_statistics

theorem labelledTripleOrbit_max (c a b : ℕ) (hba : b ≤ a) (hac : a ≤ c)
    (u : ℕ × ℕ × ℕ) (hu : u ∈ labelledTripleOrbit c a b) :
    max u.1 (max u.2.1 u.2.2) = c := by
  have hbc : b ≤ c := hba.trans hac
  simp only [labelledTripleOrbit, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · change max c (max a b) = c
    rw [max_eq_left hba, max_eq_left hac]
  · change max c (max b a) = c
    rw [max_eq_right hba, max_eq_left hac]
  · change max a (max c b) = c
    rw [max_eq_left hbc, max_eq_right hac]
  · change max a (max b c) = c
    rw [max_eq_right hbc, max_eq_right hac]
  · change max b (max c a) = c
    rw [max_eq_left hac, max_eq_right hbc]
  · change max b (max a c) = c
    rw [max_eq_right hac, max_eq_right hbc]
#print axioms Paper7MomentCounts.labelledTripleOrbit_max

theorem labelledTripleOrbit_card (c a b : ℕ) (hba : b ≤ a) (hac : a ≤ c) :
    (labelledTripleOrbit c a b).card = labelledSortedTripleMultiplicity c a b := by
  classical
  by_cases hca : c = a
  · subst c
    by_cases hab : a = b
    · subst a
      simp [labelledTripleOrbit, labelledSortedTripleMultiplicity]
    · have hba' : b ≠ a := Ne.symm hab
      simp_all [labelledTripleOrbit, labelledSortedTripleMultiplicity]
  · by_cases hab : a = b
    · subst a
      have hbc : b ≠ c := Ne.symm hca
      simp_all [labelledTripleOrbit, labelledSortedTripleMultiplicity]
    · have hcb : c ≠ b := by omega
      have hac' : a ≠ c := Ne.symm hca
      have hba' : b ≠ a := Ne.symm hab
      have hbc : b ≠ c := Ne.symm hcb
      simp_all [labelledTripleOrbit, labelledSortedTripleMultiplicity]
#print axioms Paper7MomentCounts.labelledTripleOrbit_card

theorem labelledTripleOrbit_sorted_exists (u : ℕ × ℕ × ℕ) :
    ∃ c a b : ℕ, b ≤ a ∧ a ≤ c ∧ u ∈ labelledTripleOrbit c a b := by
  rcases u with ⟨x, y, z⟩
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · refine ⟨z, y, x, hxy, hyz, ?_⟩
      simp [labelledTripleOrbit]
    · rcases le_total x z with hxz | hzx
      · refine ⟨y, z, x, hxz, hzy, ?_⟩
        simp [labelledTripleOrbit]
      · refine ⟨y, x, z, hzx, hxy, ?_⟩
        simp [labelledTripleOrbit]
  · rcases le_total x z with hxz | hzx
    · refine ⟨z, x, y, hyx, hxz, ?_⟩
      simp [labelledTripleOrbit]
    · rcases le_total y z with hyz | hzy
      · refine ⟨x, z, y, hyz, hzx, ?_⟩
        simp [labelledTripleOrbit]
      · refine ⟨x, y, z, hzy, hyx, ?_⟩
        simp [labelledTripleOrbit]
#print axioms Paper7MomentCounts.labelledTripleOrbit_sorted_exists

theorem labelled_sorted_triple_decode_complete (A B c a b : ℕ)
    (hba : b ≤ a) (hac : a ≤ c)
    (hsum : c + a + b = A) (hsq : c^2 + a^2 + b^2 = B) :
    c ∈ labelledTripleScalarRange A B ∧
      B6SortedTripleDiscriminantAccept A B c ∧
      labelledTripleHigh A B c = a ∧ labelledTripleLow A B c = b := by
  have hs : A - c = a + b := by omega
  have hd : (a-b) + b = a := Nat.sub_add_cancel hba
  have hA : A = a+b+c := by omega
  have hB : B = a^2+b^2+c^2 := by omega
  have hr : labelledTripleRoot A B c = a-b := by
    rw [hA, hB]
    exact labelled_sorted_triple_root_recovers a b c hba
  have ha : labelledTripleHigh A B c = a := by
    unfold labelledTripleHigh
    rw [hs, hr]
    omega
  have hb : labelledTripleLow A B c = b := by
    unfold labelledTripleLow
    rw [hs, hr]
    omega
  have hp : 2*(a^2+b^2) = (a+b)^2+(a-b)^2 :=
    labelled_pair_squares_from_halves (a+b) (a-b) a b
      (by omega) (by omega) (by omega)
  have hguard : B6SortedTripleDiscriminantAccept A B c := by
    unfold B6SortedTripleDiscriminantAccept
    rw [hs, hr]
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hrange : c ∈ labelledTripleScalarRange A B := by
    apply Finset.mem_Icc.mpr
    refine ⟨by omega, le_min (by omega) ?_⟩
    exact Nat.le_sqrt'.mpr (by omega)
  exact ⟨hrange, hguard, ha, hb⟩
#print axioms Paper7MomentCounts.labelled_sorted_triple_decode_complete

def labelledTripleCapacitySupport (A B : ℕ) : Finset ℕ :=
  (labelledTripleScalarRange A B).filter (B6SortedTripleDiscriminantAccept A B)
#print axioms Paper7MomentCounts.labelledTripleCapacitySupport

def labelledTripleCapacityRealization (A B : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (labelledTripleCapacitySupport A B).biUnion (fun c =>
    labelledTripleOrbit c (labelledTripleHigh A B c) (labelledTripleLow A B c))
#print axioms Paper7MomentCounts.labelledTripleCapacityRealization

theorem labelledTripleCapacityRealization_mem_iff (A B : ℕ) (u : ℕ × ℕ × ℕ) :
    u ∈ labelledTripleCapacityRealization A B ↔
      u.1 + u.2.1 + u.2.2 = A ∧ u.1^2 + u.2.1^2 + u.2.2^2 = B := by
  unfold labelledTripleCapacityRealization
  constructor
  · intro hu
    obtain ⟨c, hc, huc⟩ := Finset.mem_biUnion.mp hu
    have hg : B6SortedTripleDiscriminantAccept A B c :=
      (Finset.mem_filter.mp hc).2
    have hs := labelled_sorted_triple_decode_sound A B c hg
    have ho := labelledTripleOrbit_statistics c
      (labelledTripleHigh A B c) (labelledTripleLow A B c) u huc
    exact ⟨ho.1.trans hs.2.2.1, ho.2.trans hs.2.2.2⟩
  · intro hu
    obtain ⟨c, a, b, hba, hac, horbit⟩ := labelledTripleOrbit_sorted_exists u
    have ho := labelledTripleOrbit_statistics c a b u horbit
    have hsum : c+a+b = A := ho.1.symm.trans hu.1
    have hsq : c^2+a^2+b^2 = B := ho.2.symm.trans hu.2
    obtain ⟨hrange, hguard, ha, hb⟩ :=
      labelled_sorted_triple_decode_complete A B c a b hba hac hsum hsq
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_filter.mpr ⟨hrange, hguard⟩, ?_⟩
    simpa only [ha, hb] using horbit
#print axioms Paper7MomentCounts.labelledTripleCapacityRealization_mem_iff

theorem labelledTripleCapacity_orbits_disjoint (A B : ℕ) :
    (↑(labelledTripleCapacitySupport A B) : Set ℕ).PairwiseDisjoint
      (fun c => labelledTripleOrbit c
        (labelledTripleHigh A B c) (labelledTripleLow A B c)) := by
  intro c hc d hd hcd
  apply Finset.disjoint_left.mpr
  intro u huc hud
  have hcg : B6SortedTripleDiscriminantAccept A B c :=
    (Finset.mem_filter.mp hc).2
  have hdg : B6SortedTripleDiscriminantAccept A B d :=
    (Finset.mem_filter.mp hd).2
  have hcs := labelled_sorted_triple_decode_sound A B c hcg
  have hds := labelled_sorted_triple_decode_sound A B d hdg
  have hmc := labelledTripleOrbit_max c (labelledTripleHigh A B c)
    (labelledTripleLow A B c) hcs.1 hcs.2.1 u huc
  have hmd := labelledTripleOrbit_max d (labelledTripleHigh A B d)
    (labelledTripleLow A B d) hds.1 hds.2.1 u hud
  exact hcd (hmc.symm.trans hmd)
#print axioms Paper7MomentCounts.labelledTripleCapacity_orbits_disjoint

theorem labelledTripleCapacityRealization_card (A B : ℕ) :
    (labelledTripleCapacityRealization A B).card =
      ∑ c ∈ labelledTripleScalarRange A B,
        if B6SortedTripleDiscriminantAccept A B c then
          labelledSortedTripleMultiplicity c
            (labelledTripleHigh A B c) (labelledTripleLow A B c) else 0 := by
  unfold labelledTripleCapacityRealization
  rw [Finset.card_biUnion (labelledTripleCapacity_orbits_disjoint A B)]
  calc
    (∑ c ∈ labelledTripleCapacitySupport A B,
        (labelledTripleOrbit c (labelledTripleHigh A B c)
          (labelledTripleLow A B c)).card) =
        ∑ c ∈ labelledTripleCapacitySupport A B,
          labelledSortedTripleMultiplicity c
            (labelledTripleHigh A B c) (labelledTripleLow A B c) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hg : B6SortedTripleDiscriminantAccept A B c :=
        (Finset.mem_filter.mp hc).2
      have hs := labelled_sorted_triple_decode_sound A B c hg
      exact labelledTripleOrbit_card c (labelledTripleHigh A B c)
        (labelledTripleLow A B c) hs.1 hs.2.1
    _ = ∑ c ∈ labelledTripleScalarRange A B,
        if B6SortedTripleDiscriminantAccept A B c then
          labelledSortedTripleMultiplicity c
            (labelledTripleHigh A B c) (labelledTripleLow A B c) else 0 := by
      simp only [labelledTripleCapacitySupport, Finset.sum_filter]
#print axioms Paper7MomentCounts.labelledTripleCapacityRealization_card

def labelledTripleCapacityTupleEquiv (A B : ℕ) :
    {z : Fin 3 → ℕ // (∑ i, z i) = A ∧ (∑ i, z i^2) = B} ≃
      {u : ℕ × ℕ × ℕ //
        u.1 + u.2.1 + u.2.2 = A ∧ u.1^2 + u.2.1^2 + u.2.2^2 = B} where
  toFun z := ⟨(z.val 0, z.val 1, z.val 2), by
    simpa [Fin.sum_univ_succ, add_assoc] using z.property⟩
  invFun u := ⟨![u.val.1, u.val.2.1, u.val.2.2], by
    simpa [Fin.sum_univ_succ, add_assoc] using u.property⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv u := by
    apply Subtype.ext
    rfl
#print axioms Paper7MomentCounts.labelledTripleCapacityTupleEquiv

def labelledTripleTupleRealizationEquiv (A B : ℕ) :
    {u : ℕ × ℕ × ℕ //
      u.1 + u.2.1 + u.2.2 = A ∧ u.1^2 + u.2.1^2 + u.2.2^2 = B} ≃
      ↥(labelledTripleCapacityRealization A B) :=
  Equiv.subtypeEquivRight (fun u => (labelledTripleCapacityRealization_mem_iff A B u).symm)
#print axioms Paper7MomentCounts.labelledTripleTupleRealizationEquiv

theorem labelledExactCapacityCard_three_eq_discriminant (A B : ℕ) :
    labelledExactCapacityCard 3 A B =
      ∑ c ∈ labelledTripleScalarRange A B,
        if B6SortedTripleDiscriminantAccept A B c then
          labelledSortedTripleMultiplicity c
            (labelledTripleHigh A B c) (labelledTripleLow A B c) else 0 := by
  unfold labelledExactCapacityCard
  calc
    Nat.card {z : Fin 3 → ℕ // (∑ i, z i) = A ∧ (∑ i, z i^2) = B} =
        Nat.card ↥(labelledTripleCapacityRealization A B) :=
      Nat.card_congr ((labelledTripleCapacityTupleEquiv A B).trans
        (labelledTripleTupleRealizationEquiv A B))
    _ = (labelledTripleCapacityRealization A B).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = ∑ c ∈ labelledTripleScalarRange A B,
        if B6SortedTripleDiscriminantAccept A B c then
          labelledSortedTripleMultiplicity c
            (labelledTripleHigh A B c) (labelledTripleLow A B c) else 0 :=
      labelledTripleCapacityRealization_card A B
#print axioms Paper7MomentCounts.labelledExactCapacityCard_three_eq_discriminant

theorem labelledTripleQWeight_zero (c a b : ℕ) :
    labelledTripleQWeight c a b 0 = 1 := by
  have hzero : labelledPositiveTriangular 0 = 1 := by
    norm_num [labelledPositiveTriangular]
  have hneg (r : ℤ) (hr : r < 0) : labelledPositiveTriangular r = 0 := by
    exact ite_eq_left hr
  simp only [labelledTripleQWeight, Nat.cast_zero]
  simp only [hzero,
    hneg ((0 : ℤ) - c - 1) (by omega),
    hneg ((0 : ℤ) - a - 1) (by omega),
    hneg ((0 : ℤ) - b - 1) (by omega),
    hneg ((0 : ℤ) - c - a - 2) (by omega),
    hneg ((0 : ℤ) - c - b - 2) (by omega),
    hneg ((0 : ℤ) - a - b - 2) (by omega),
    hneg ((0 : ℤ) - c - a - b - 3) (by omega), sub_zero, add_zero]
#print axioms Paper7MomentCounts.labelledTripleQWeight_zero

theorem labelledTripleDiscriminantKernel_zero_eq_actual_capacity (A B : ℕ) :
    labelledTripleDiscriminantKernel A B 0 = (labelledExactCapacityCard 3 A B : ℤ) := by
  rw [labelledExactCapacityCard_three_eq_discriminant]
  unfold labelledTripleDiscriminantKernel
  push_cast
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hg : B6SortedTripleDiscriminantAccept A B c
  · simp [hg, labelledTripleQWeight_zero]
  · simp [hg]
#print axioms Paper7MomentCounts.labelledTripleDiscriminantKernel_zero_eq_actual_capacity

end Paper7MomentCounts
