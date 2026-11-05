import Research.Backfill.Paper7.MomentB4GapSum

/-! Source-only candidate. Actual distinct-orbit cardinalities for sorted four
tuples, proved through multiplicity factorials. No permutation-witness count,
candidate list, or numerical B1 total is substituted for an orbit cardinality. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentReduction
open Paper7Budget Paper7SortedRows Paper7SortedGaps Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4RawOrbitWeight_mul_multiplicities (z : Fin 4 → ℕ) :
    b4RawOrbitWeight z *
      (∏ v ∈ Finset.univ.image z,
        (Fintype.card {i : Fin 4 // z i = v}).factorial) = 24 := by
  let x : BoundedTuple 4 (∑ i, z i) := ⟨z, le_rfl⟩
  have h := orbitWeight_mul_multiplicities x
  rw [b4_orbitWeight_eq_raw] at h
  exact h
#print axioms Paper7MomentReduction.b4RawOrbitWeight_mul_multiplicities

theorem b4_vector_image (a b c d : ℕ) :
    Finset.univ.image (![a, b, c, d] : Fin 4 → ℕ) = {a, b, c, d} := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    fin_cases i <;> simp_all
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
#print axioms Paper7MomentReduction.b4_vector_image

theorem b4_vector_fibre_card (a b c d v : ℕ) :
    Fintype.card {i : Fin 4 // ![a, b, c, d] i = v} =
      (if a = v then 1 else 0) + (if b = v then 1 else 0) +
        (if c = v then 1 else 0) + (if d = v then 1 else 0) := by
  calc
    Fintype.card {i : Fin 4 // ![a, b, c, d] i = v} =
        (Finset.univ.filter (fun i : Fin 4 => ![a, b, c, d] i = v)).card :=
      Fintype.card_subtype _
    _ = ∑ i : Fin 4, if ![a, b, c, d] i = v then (1 : ℕ) else 0 :=
      Finset.card_filter _ _
    _ = (if a = v then 1 else 0) + (if b = v then 1 else 0) +
        (if c = v then 1 else 0) + (if d = v then 1 else 0) :=
      Fin.sum_univ_four _
#print axioms Paper7MomentReduction.b4_vector_fibre_card

theorem b4RawOrbitWeight_vector_mul (a b c d : ℕ) :
    b4RawOrbitWeight ![a, b, c, d] *
      (∏ v ∈ ({a, b, c, d} : Finset ℕ),
        ((if a = v then 1 else 0) + (if b = v then 1 else 0) +
          (if c = v then 1 else 0) + (if d = v then 1 else 0)).factorial) = 24 := by
  have h := b4RawOrbitWeight_mul_multiplicities ![a, b, c, d]
  rw [b4_vector_image] at h
  simp_rw [b4_vector_fibre_card] at h
  exact h
#print axioms Paper7MomentReduction.b4RawOrbitWeight_vector_mul

/-- Eight adjacent-equality patterns, with the five possible orbit sizes. -/
def b4PatternWeight (z : Fin 4 → ℕ) : ℕ :=
  if z 0 = z 1 then
    if z 1 = z 2 then
      if z 2 = z 3 then 1 else 4
    else
      if z 2 = z 3 then 6 else 12
  else
    if z 1 = z 2 then
      if z 2 = z 3 then 4 else 12
    else
      if z 2 = z 3 then 12 else 24
#print axioms Paper7MomentReduction.b4PatternWeight

theorem b4RawOrbitWeight_vector_eq_pattern (a b c d : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    b4RawOrbitWeight ![a, b, c, d] = b4PatternWeight ![a, b, c, d] := by
  have h := b4RawOrbitWeight_vector_mul a b c d
  by_cases hab' : a = b
  · subst b
    by_cases hac' : a = c
    · subst c
      by_cases had' : a = d
      · subst d
        simp_all [b4PatternWeight]; norm_num at *; omega
      · simp_all [b4PatternWeight, eq_comm]; norm_num at *; omega
    · by_cases hcd' : c = d
      · subst d
        simp_all [b4PatternWeight, eq_comm]; omega
      · have had' : a ≠ d := by omega
        simp_all [b4PatternWeight, eq_comm]; omega
  · by_cases hbc' : b = c
    · subst c
      by_cases hbd' : b = d
      · subst d
        simp_all [b4PatternWeight, eq_comm]; norm_num at *; omega
      · have had' : a ≠ d := by omega
        simp_all [b4PatternWeight, eq_comm]; omega
    · have hac' : a ≠ c := by omega
      by_cases hcd' : c = d
      · subst d
        simp_all [b4PatternWeight, eq_comm]; omega
      · have had' : a ≠ d := by omega
        have hbd' : b ≠ d := by omega
        simp_all [b4PatternWeight, eq_comm]
#print axioms Paper7MomentReduction.b4RawOrbitWeight_vector_eq_pattern

theorem b4RawOrbitWeight_eq_pattern (z : Fin 4 → ℕ) (hz : Monotone z) :
    b4RawOrbitWeight z = b4PatternWeight z := by
  have heta : ![z 0, z 1, z 2, z 3] = z := by
    funext i
    fin_cases i <;> rfl
  have h := b4RawOrbitWeight_vector_eq_pattern (z 0) (z 1) (z 2) (z 3)
    (hz (by decide)) (hz (by decide)) (hz (by decide))
  simpa only [heta] using h
#print axioms Paper7MomentReduction.b4RawOrbitWeight_eq_pattern

/-- Equality of adjacent prefix sums is exactly vanishing of the intervening gap. -/
def b4GapPatternWeight (b c d : ℕ) : ℕ :=
  if b = 0 then
    if c = 0 then
      if d = 0 then 1 else 4
    else
      if d = 0 then 6 else 12
  else
    if c = 0 then
      if d = 0 then 4 else 12
    else
      if d = 0 then 12 else 24
#print axioms Paper7MomentReduction.b4GapPatternWeight

theorem b4RawOrbitWeight_prefix_eq_pattern (a b c d : ℕ) :
    b4RawOrbitWeight (prefixRow ![a, b, c, d]) = b4GapPatternWeight b c d := by
  have h := b4RawOrbitWeight_vector_eq_pattern
    a (a + b) (a + b + c) (a + b + c + d) (by omega) (by omega) (by omega)
  have hb : (a = a + b) ↔ b = 0 := by omega
  have hc : (a + b = a + b + c) ↔ c = 0 := by omega
  have hd : (a + b + c = a + b + c + d) ↔ d = 0 := by omega
  change b4RawOrbitWeight (prefixRow ![a, b, c, d]) =
    (if a = a + b then
      if a + b = a + b + c then
        if a + b + c = a + b + c + d then 1 else 4
      else
        if a + b + c = a + b + c + d then 6 else 12
    else
      if a + b = a + b + c then
        if a + b + c = a + b + c + d then 4 else 12
      else
        if a + b + c = a + b + c + d then 12 else 24) at h
  simpa only [hb, hc, hd, b4GapPatternWeight] using h
#print axioms Paper7MomentReduction.b4RawOrbitWeight_prefix_eq_pattern

theorem b4RawGapContribution_eq_pattern (a b c d : ℕ) :
    b4RawGapContribution ![a, b, c, d] =
      b4GapPatternWeight b c d *
        b4RowContribution ![a, a + b, a + b + c, a + b + c + d] := by
  unfold b4RawGapContribution
  rw [b4RawOrbitWeight_prefix_eq_pattern]
  rfl
#print axioms Paper7MomentReduction.b4RawGapContribution_eq_pattern

end Paper7MomentReduction
