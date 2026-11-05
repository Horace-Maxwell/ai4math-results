import Mathlib

/-! Finite signed-multiplicity bookkeeping; no graph or spectral hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Paper7OddIntegral

def symmetricSupport (s : Multiset ℤ) : Finset ℤ :=
  s.toFinset ∪ s.toFinset.image (fun z => -z)
#print axioms Paper7OddIntegral.symmetricSupport

theorem mem_symmetricSupport (s : Multiset ℤ) (z : ℤ) :
    z ∈ symmetricSupport s ↔ z ∈ s ∨ -z ∈ s := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact Or.inl (Multiset.mem_toFinset.mp h)
    · obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp h
      right
      have hv' : v = -z := by omega
      simpa only [hv'] using Multiset.mem_toFinset.mp hv
  · rintro (h | h)
    · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr h)
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨-z, Multiset.mem_toFinset.mpr h, neg_neg z⟩
#print axioms Paper7OddIntegral.mem_symmetricSupport

theorem symmetricSupport_neg (s : Multiset ℤ) (z : ℤ) :
    -z ∈ symmetricSupport s ↔ z ∈ symmetricSupport s := by
  simp only [mem_symmetricSupport, neg_neg, or_comm]
#print axioms Paper7OddIntegral.symmetricSupport_neg

def positiveSupport (s : Multiset ℤ) : Finset ℤ :=
  (symmetricSupport s).filter (fun z => 2 ≤ z)
#print axioms Paper7OddIntegral.positiveSupport

def asymmetricSupport (s : Multiset ℤ) : Finset ℤ :=
  (positiveSupport s).filter (fun z => s.count z ≠ s.count (-z))
#print axioms Paper7OddIntegral.asymmetricSupport

theorem sum_map_on_symmetricSupport (s : Multiset ℤ) (F : ℤ → ℝ) :
    (s.map F).sum = ∑ z ∈ symmetricSupport s, (s.count z : ℝ) * F z := by
  classical
  calc
    _ = ∑ z ∈ s.toFinset, (s.count z : ℝ) * F z := by
      simpa only [nsmul_eq_mul] using Finset.sum_multiset_map_count s F
    _ = ∑ z ∈ symmetricSupport s, (s.count z : ℝ) * F z := by
      apply Finset.sum_subset (Finset.subset_union_left)
      intro z _ hz
      have hnot : z ∉ s := by simpa only [Multiset.mem_toFinset] using hz
      rw [Multiset.count_eq_zero.mpr hnot, Nat.cast_zero, zero_mul]
#print axioms Paper7OddIntegral.sum_map_on_symmetricSupport

theorem positiveSupport_disjoint_neg (s : Multiset ℤ) :
    Disjoint (positiveSupport s) ((positiveSupport s).image (fun z => -z)) := by
  apply Finset.disjoint_left.mpr
  intro z hz hn
  obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hn
  have hz2 := (Finset.mem_filter.mp hz).2
  have hv2 := (Finset.mem_filter.mp hv).2
  omega
#print axioms Paper7OddIntegral.positiveSupport_disjoint_neg

theorem largeSupport_eq_pair (s : Multiset ℤ) :
    (symmetricSupport s).filter (fun z => 2 ≤ |z|) =
      positiveSupport s ∪ (positiveSupport s).image (fun z => -z) := by
  apply Finset.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hzS, ha⟩ := Finset.mem_filter.mp hz
    by_cases hpos : 0 ≤ z
    · rw [abs_of_nonneg hpos] at ha
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzS, ha⟩)
    · have hneg : z ≤ 0 := by omega
      rw [abs_of_nonpos hneg] at ha
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨-z, Finset.mem_filter.mpr ⟨(symmetricSupport_neg s z).mpr hzS, ha⟩,
        neg_neg z⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨hzS, hz2⟩ := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr
      exact ⟨hzS, by rw [abs_of_nonneg (by omega : 0 ≤ z)]; exact hz2⟩
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hvS, hv2⟩ := Finset.mem_filter.mp hv
      apply Finset.mem_filter.mpr
      refine ⟨(symmetricSupport_neg s v).mpr hvS, ?_⟩
      rw [abs_neg, abs_of_nonneg (by omega : 0 ≤ v)]
      exact hv2
#print axioms Paper7OddIntegral.largeSupport_eq_pair

theorem odd_sum_pairing (s : Multiset ℤ) (F : ℤ → ℝ)
    (hodd : ∀ z, F (-z) = -F z) (hsmall : ∀ z, ¬ 2 ≤ |z| → F z = 0) :
    (s.map F).sum = ∑ z ∈ asymmetricSupport s,
      ((s.count z : ℝ) - (s.count (-z) : ℝ)) * F z := by
  classical
  have hlarge :
      (∑ z ∈ (symmetricSupport s).filter (fun z => 2 ≤ |z|), (s.count z : ℝ) * F z) =
      ∑ z ∈ symmetricSupport s, (s.count z : ℝ) * F z := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hz hn
    have hzsmall : ¬ 2 ≤ |z| := by
      intro h; exact hn (Finset.mem_filter.mpr ⟨hz, h⟩)
    rw [hsmall z hzsmall, mul_zero]
  have hfilter :
      (∑ z ∈ asymmetricSupport s, ((s.count z : ℝ) - (s.count (-z) : ℝ)) * F z) =
      ∑ z ∈ positiveSupport s, ((s.count z : ℝ) - (s.count (-z) : ℝ)) * F z := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hz hn
    have heq : s.count z = s.count (-z) := by
      by_contra heq
      exact hn (Finset.mem_filter.mpr ⟨hz, heq⟩)
    rw [heq, sub_self, zero_mul]
  rw [sum_map_on_symmetricSupport, ← hlarge, largeSupport_eq_pair,
    Finset.sum_union (positiveSupport_disjoint_neg s),
    Finset.sum_image neg_injective.injOn]
  rw [hfilter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [hodd]
  ring
#print axioms Paper7OddIntegral.odd_sum_pairing

/-- Every distinct asymmetric positive value contributes at least one square. -/
theorem asymmetric_support_square_le (s : Multiset ℤ) :
    (∑ z ∈ asymmetricSupport s, (z : ℝ) ^ 2) ≤
      (s.map (fun z => (z : ℝ) ^ 2)).sum := by
  classical
  let S := asymmetricSupport s
  have hpos (z : ℤ) (hz : z ∈ S) : 2 ≤ z :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
  have hdisj : Disjoint S (S.image (fun z => -z)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hn
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hn
    have := hpos z hz
    have := hpos v hv
    omega
  have hsub : S ∪ S.image (fun z => -z) ⊆ symmetricSupport s := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      exact (symmetricSupport_neg s v).mpr
        (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1
  have hle :
      (∑ z ∈ S ∪ S.image (fun z => -z), (s.count z : ℝ) * (z : ℝ) ^ 2) ≤
      ∑ z ∈ symmetricSupport s, (s.count z : ℝ) * (z : ℝ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro z _ _
    positivity
  rw [Finset.sum_union hdisj, Finset.sum_image neg_injective.injOn,
    ← Finset.sum_add_distrib] at hle
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map]
  rw [sum_map_on_symmetricSupport]
  apply le_trans _ hle
  apply Finset.sum_le_sum
  intro z hz
  have hne := (Finset.mem_filter.mp hz).2
  have hnat : 1 ≤ s.count z + s.count (-z) := by omega
  have hreal : (1 : ℝ) ≤ (s.count z : ℝ) + (s.count (-z) : ℝ) := by
    exact_mod_cast hnat
  have hsquare : 0 ≤ (z : ℝ) ^ 2 := sq_nonneg _
  simp only [Int.cast_neg, neg_sq]
  nlinarith
#print axioms Paper7OddIntegral.asymmetric_support_square_le

end Paper7OddIntegral
