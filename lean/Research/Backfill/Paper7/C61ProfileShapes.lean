import Research.Backfill.Paper7.C61ProfileCore

/-! Analytic coverage of the finite profile space, with no enumerated table.
Indices 0,...,4 mean eigenvalues 2,...,6. Each stored digit is at most two. -/
set_option autoImplicit false
namespace Paper7C61Profile
open scoped BigOperators

def c61 : Fin 5 → Fin 3 := ![2, 2, 1, 0, 0]
#print axioms Paper7C61Profile.c61

def Shapes (m : Fin 5 → Fin 3) : Prop :=
  ((m 1).val = 1 ∧ (m 2).val = 0 ∧ (m 3).val = 0 ∧ (m 4).val = 0) ∨
  ((m 2).val = 1 ∧ (m 3).val = 0 ∧ (m 4).val = 0) ∨
  ((m 3).val = 1 ∧ (m 4).val = 0 ∧
    (((m 2).val = 0 ∧ (m 1).val ≤ 1) ∨
      ((m 2).val = 1 ∧ (m 1).val = 0 ∧ (m 0).val = 0))) ∨
  ((m 4).val = 1 ∧ (m 3).val = 0 ∧ (m 2).val = 0 ∧
    (m 1).val = 0 ∧ (m 0).val ≤ 1)
#print axioms Paper7C61Profile.Shapes

theorem admissible_iff_shapes (m : Fin 5 → Fin 3) : Admissible m ↔ Shapes m := by
  have h0 := (m 0).isLt
  have h1 := (m 1).isLt
  have h2 := (m 2).isLt
  have h3 := (m 3).isLt
  have h4 := (m 4).isLt
  have hc : card m = (m 0).val + (m 1).val + (m 2).val + (m 3).val + (m 4).val := by
    simp [card, Fin.sum_univ_succ, Nat.add_assoc]
  have hs : square m = 4 * (m 0).val + 9 * (m 1).val + 16 * (m 2).val +
      25 * (m 3).val + 36 * (m 4).val := by
    norm_num [square, value, Fin.sum_univ_succ, Nat.mul_comm, Nat.add_assoc]
  constructor
  · rintro ⟨_hcard, hsq, r, hr, hm, hz⟩
    rw [hs] at hsq
    fin_cases r
    · norm_num [value] at hr
    · exact Or.inl ⟨hm, hz 2 (by decide), hz 3 (by decide), hz 4 (by decide)⟩
    · exact Or.inr (Or.inl ⟨hm, hz 3 (by decide), hz 4 (by decide)⟩)
    · apply Or.inr; apply Or.inr; apply Or.inl
      have h4z := hz 4 (by decide)
      refine ⟨hm, h4z, ?_⟩
      change (m 3).val = 1 at hm
      by_cases h2z : (m 2).val = 0
      · exact Or.inl ⟨h2z, by omega⟩
      · exact Or.inr ⟨by omega, by omega, by omega⟩
    · apply Or.inr; apply Or.inr; apply Or.inr
      change (m 4).val = 1 at hm
      exact ⟨hm, by omega, by omega, by omega, by omega⟩
  · intro h
    rcases h with ⟨hm1, hm2, hm3, hm4⟩ | ⟨hm2, hm3, hm4⟩ |
      ⟨hm3, hm4, hh⟩ | ⟨hm4, hm3, hm2, hm1, hm0⟩
    · refine ⟨by rw [hc]; omega, by rw [hs]; omega, 1, by decide, hm1, ?_⟩
      intro i hi
      fin_cases i <;> norm_num at hi <;> assumption
    · refine ⟨by rw [hc]; omega, by rw [hs]; omega, 2, by decide, hm2, ?_⟩
      intro i hi
      fin_cases i <;> norm_num at hi <;> assumption
    · have hcard : card m ≤ 5 := by rw [hc]; rcases hh with hh | hh <;> omega
      have hsq : square m ≤ 42 := by rw [hs]; rcases hh with hh | hh <;> omega
      refine ⟨hcard, hsq, 3, by decide, hm3, ?_⟩
      intro i hi
      fin_cases i <;> norm_num at hi
      assumption
    · refine ⟨by rw [hc]; omega, by rw [hs]; omega, 4, by decide, hm4, ?_⟩
      intro i hi
      have := i.isLt
      omega
#print axioms Paper7C61Profile.admissible_iff_shapes

theorem actual_shapes (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : BackfillPaper7.Challenge.nOf 6 p q ≤ 42)
    (hG : BackfillPaper7.Challenge.IsIntegralGraph (BackfillPaper7.Challenge.SG 6 p q)) :
    Shapes (actual p q) :=
  (admissible_iff_shapes (actual p q)).mp (actual_admissible p q hp hn hG)
#print axioms Paper7C61Profile.actual_shapes

theorem card_five_unique (m : Fin 5 → Fin 3) (ha : Admissible m)
    (hc : card m = 5) : m = c61 := by
  have h0 := (m 0).isLt
  have h1 := (m 1).isLt
  have h2 := (m 2).isLt
  have h3 := (m 3).isLt
  have h4 := (m 4).isLt
  have hc' : (m 0).val + (m 1).val + (m 2).val + (m 3).val + (m 4).val = 5 := by
    simpa [card, Fin.sum_univ_succ, Nat.add_assoc] using hc
  have h := (admissible_iff_shapes m).mp ha
  rcases h with ⟨hm1, hm2, hm3, hm4⟩ | ⟨hm2, hm3, hm4⟩ |
    ⟨hm3, hm4, hh⟩ | ⟨hm4, hm3, hm2, hm1, hm0⟩
  · omega
  · have hm0 : (m 0).val = 2 := by omega
    have hm1 : (m 1).val = 2 := by omega
    funext i
    apply Fin.ext
    fin_cases i
    · exact hm0
    · exact hm1
    · exact hm2
    · exact hm3
    · exact hm4
  · rcases hh with hh | hh <;> omega
  · omega
#print axioms Paper7C61Profile.card_five_unique

theorem c61_square : square c61 = 42 := by
  norm_num [square, c61, value, Fin.sum_univ_succ]
#print axioms Paper7C61Profile.c61_square

end Paper7C61Profile
