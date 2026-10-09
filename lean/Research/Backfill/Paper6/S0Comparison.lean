import Research.Backfill.Paper6.ChallengeV3

/-!
# Exact comparison of the two finite-set descriptions in Paper 6

Candidate proof source, not yet compiled or accepted. All finite decisions are on
the displayed small sets. Interval membership is handled symbolically. In particular,
the complement condition retains its upper bound, so natural subtraction cannot
admit spurious values greater than 16384.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6FiniteFacts

open BackfillPaper6.V3

theorem check_S0_eq_LA : BackfillPaper6.V3.S0_eq_LA := by
  let B : Finset ℕ := {312, 314, 316, 318}
  let D : Finset ℕ := {16066, 16068, 16070, 16072}
  let I : Finset ℕ := (Finset.range 16065).filter (fun w => 320 ≤ w ∧ Even w)
  let A : Finset ℕ := (K ∪ I) ∪ K.image (fun k => 16384 - k)
  have K_split : K = W0 ∪ B := by
    change K = W0 ∪ ({312, 314, 316, 318} : Finset ℕ)
    decide +kernel
  have B_image : B.image (fun k => 16384 - k) = D := by
    change ({312, 314, 316, 318} : Finset ℕ).image (fun k => 16384 - k) =
      {16066, 16068, 16070, 16072}
    decide +kernel
  have K_image : K.image (fun k => 16384 - k) =
      W0.image (fun k => 16384 - k) ∪ D := by
    rw [K_split, Finset.image_union, B_image]
  have W0_bound : ∀ k ∈ W0, k ≤ 16384 := by decide +kernel
  have complement_mem (w : ℕ) :
      w ∈ W0.image (fun k => 16384 - k) ↔ w ≤ 16384 ∧ 16384 - w ∈ W0 := by
    constructor
    · intro hw
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
      have hbound := W0_bound k hk
      refine ⟨by omega, ?_⟩
      have hcancel : 16384 - (16384 - k) = k := by omega
      rw [hcancel]
      exact hk
    · rintro ⟨hbound, hmem⟩
      exact Finset.mem_image.mpr ⟨16384 - w, hmem, by omega⟩
  have interval_mem (w : ℕ) :
      (w ∈ B ∨ w ∈ I ∨ w ∈ D) ↔ Even w ∧ 312 ≤ w ∧ w ≤ 16384 - 312 := by
    simp only [B, D, I, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_filter, Finset.mem_range, Nat.even_iff]
    by_cases hlow : w < 320
    · omega
    · by_cases hmiddle : w ≤ 16064
      · omega
      · omega
  have base_mem (w : ℕ) :
      w ∈ A ↔
        w ∈ W0 ∨ (Even w ∧ 312 ≤ w ∧ w ≤ 16384 - 312) ∨
          (w ≤ 16384 ∧ 16384 - w ∈ W0) := by
    change w ∈ ((K ∪ I) ∪ K.image (fun k => 16384 - k)) ↔ _
    rw [K_image, K_split]
    simp only [Finset.mem_union]
    rw [complement_mem w]
    constructor
    · intro hw
      rcases hw with hwleft | hwright
      · rcases hwleft with hwWB | hwI
        · rcases hwWB with hwW | hwB
          · exact Or.inl hwW
          · exact Or.inr (Or.inl ((interval_mem w).mp (Or.inl hwB)))
        · exact Or.inr (Or.inl ((interval_mem w).mp (Or.inr (Or.inl hwI))))
      · rcases hwright with hwC | hwD
        · exact Or.inr (Or.inr hwC)
        · exact Or.inr (Or.inl ((interval_mem w).mp (Or.inr (Or.inr hwD))))
    · intro hw
      rcases hw with hwW | hwrest
      · exact Or.inl (Or.inl (Or.inl hwW))
      · rcases hwrest with hwinterval | hwC
        · rcases (interval_mem w).mpr hwinterval with hwB | hwrest
          · exact Or.inl (Or.inl (Or.inr hwB))
          · rcases hwrest with hwI | hwD
            · exact Or.inl (Or.inr hwI)
            · exact Or.inr (Or.inr hwD)
        · exact Or.inr (Or.inl hwC)
  have M_bounds : ∀ w ∈ M, Even w ∧ 312 ≤ w ∧ w ≤ 16384 - 312 := by
    decide +kernel
  have M_subset : M ⊆ A := by
    intro w hw
    exact (base_mem w).mpr (Or.inr (Or.inl (M_bounds w hw)))
  have U_subset_M : U ⊆ M := by decide +kernel
  have S0_as_difference : S0 = A \ U := rfl
  unfold BackfillPaper6.V3.S0_eq_LA
  ext w
  simp only [Finset.mem_coe, Set.mem_union, Set.mem_ofPred_eq]
  rw [S0_as_difference]
  simp only [Finset.mem_sdiff]
  rw [base_mem w]
  constructor
  · rintro ⟨hwA, hwU⟩
    by_cases hwM : w ∈ M
    · exact Or.inr ⟨hwM, hwU⟩
    · exact Or.inl ⟨hwA, hwM⟩
  · rintro (⟨hwA, hwM⟩ | ⟨hwM, hwU⟩)
    · exact ⟨hwA, fun hwU => hwM (U_subset_M hwU)⟩
    · exact ⟨(base_mem w).mp (M_subset hwM), hwU⟩

end Paper6FiniteFacts

#print axioms Paper6FiniteFacts.check_S0_eq_LA
