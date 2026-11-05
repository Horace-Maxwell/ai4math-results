import Research.Backfill.Paper7.LegacyTransfer

/-! Source-only author candidate by Codex subagent p6_binding_spotcheck.
The reported-run leaf bound uses the literal frozen run family and actual Stage
predicates. In particular, the b=22/26 A6(true) leaves are excluded by their own
admissible-count and cycle-filter conditions. No integral-spectrum, floating
guard, output-completeness, or classification assumption is used. No compilation
or kernel acceptance of this candidate is claimed. -/

set_option autoImplicit false
open scoped Classical BigOperators
noncomputable section

namespace Paper7CRTEnvelope
open BackfillPaper7.Challenge.Legacy

/-- Only the value 2 can contribute less than nine per positive count, and it
has multiplicity at most two because the frozen counts have type Fin 3. -/
theorem even_s2_posCard_lower (b : ℕ) (s : SpectralCounts) (he : Even b) :
    9 * (posCard s : ℤ) ≤ s2 b s + 10 := by
  have hterm (i : Fin 8) :
      9 * ((s.1 i).val : ℤ) ≤
        ((s.1 i).val : ℤ) * (value i : ℤ) ^ 2 +
          (if i = 0 then 10 else 0) := by
    by_cases hi : i = 0
    · subst i
      have hc : ((s.1 (0 : Fin 8)).val : ℤ) ≤ 2 := by
        exact_mod_cast (show (s.1 (0 : Fin 8)).val ≤ 2 by omega)
      rw [ite_eq_left (rfl : (0 : Fin 8) = 0)]
      change 9 * ((s.1 (0 : Fin 8)).val : ℤ) ≤
        ((s.1 (0 : Fin 8)).val : ℤ) * 4 + 10
      omega
    · have hi0 : i.val ≠ 0 := by
        intro h
        exact hi (Fin.ext h)
      have hv : (3 : ℤ) ≤ (value i : ℤ) := by
        have hvN : 3 ≤ value i := by unfold value; omega
        exact_mod_cast hvN
      have hv2 : (9 : ℤ) ≤ (value i : ℤ) ^ 2 := by nlinarith
      have hc : (0 : ℤ) ≤ (s.1 i).val := by positivity
      rw [ite_eq_right hi, add_zero]
      calc
        9 * ((s.1 i).val : ℤ) = ((s.1 i).val : ℤ) * 9 := mul_comm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hv2 hc
  calc
    9 * (posCard s : ℤ) = ∑ i : Fin 8, 9 * ((s.1 i).val : ℤ) := by
      rw [posCard, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ i : Fin 8, (((s.1 i).val : ℤ) * (value i : ℤ) ^ 2 +
        (if i = 0 then 10 else 0)) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = s2 b s + 10 := by simp [s2, he, Finset.sum_add_distrib]
#print axioms Paper7CRTEnvelope.even_s2_posCard_lower

theorem admissible_even_42_posCard_le_five (b : ℕ) (s : SpectralCounts)
    (he : Even b) (hs : Admissible true b 42 s) : posCard s ≤ 5 := by
  have hupper : s2 b s ≤ 42 := by
    simpa only [he, ite_true, Nat.cast_ofNat] using hs.1.2.1
  have hlower := even_s2_posCard_lower b s he
  have hcard : (posCard s : ℤ) ≤ 5 := by omega
  exact_mod_cast hcard
#print axioms Paper7CRTEnvelope.admissible_even_42_posCard_le_five

theorem cyclic_positive_twenty_two : cyclicPositive 22 = 7 := by
  decide +kernel
#print axioms Paper7CRTEnvelope.cyclic_positive_twenty_two

theorem cyclic_positive_twenty_six : cyclicPositive 26 = 9 := by
  decide +kernel
#print axioms Paper7CRTEnvelope.cyclic_positive_twenty_six

/-- The exclusion uses the actual MomentPass member of AReaches. -/
theorem cycle_filtered_areaches_not_large (countBound : Bool) (b : ℕ)
    (hb : b = 22 ∨ b = 26) (x : PQ b) (hx : AReaches true countBound b 42 x) : False := by
  obtain ⟨s, hs, _⟩ := hx.2.2.1
  have he : Even b := by rcases hb with rfl | rfl <;> norm_num
  have hcard := admissible_even_42_posCard_le_five b s he hs
  have hcycle := (hs.2 rfl).1
  rcases hb with rfl | rfl
  · rw [cyclic_positive_twenty_two] at hcycle
    omega
  · rw [cyclic_positive_twenty_six] at hcycle
    omega
#print axioms Paper7CRTEnvelope.cycle_filtered_areaches_not_large

/-- The cap is derived from the explicit run-family cases. -/
theorem reported_a_run_N_le_fortynine (v : SearchVersion) (b N : ℕ)
    (hRun : ReportedARun v b N) : N ≤ 49 := by
  rcases hRun with ⟨_, hcases⟩ | ⟨_, hcases⟩ | ⟨_, hcases⟩ | ⟨_, _, hN⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcases
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcases
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcases
    omega
  · omega
#print axioms Paper7CRTEnvelope.reported_a_run_N_le_fortynine

/-- Every reported A leaf satisfies the budget through its actual A stage. -/
theorem reported_a_leaf_budget (v : SearchVersion) (b N : ℕ)
    (hRun : ReportedARun v b N) (x : PQ b) (hx : x ∈ LeafSet v b N) :
    Budget b N x := by
  rcases hRun with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
  all_goals exact hx.2.1
#print axioms Paper7CRTEnvelope.reported_a_leaf_budget

/-- The literal reported run family has no surviving A leaf with b greater than 18. -/
theorem reported_a_leaf_b_le_eighteen (v : SearchVersion) (b N : ℕ)
    (hRun : ReportedARun v b N) (x : PQ b) (hx : x ∈ LeafSet v b N) : b ≤ 18 := by
  rcases hRun with ⟨rfl, hcases⟩ | ⟨rfl, hcases⟩ | ⟨rfl, hcases⟩ |
    ⟨rfl, rfl, rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcases
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcases
    omega
  · by_contra hbig
    have hlarge : (b = 22 ∨ b = 26) ∧ N = 42 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hcases
      omega
    rcases hlarge with ⟨hb, rfl⟩
    exact cycle_filtered_areaches_not_large true b hb x hx.2
  · norm_num
#print axioms Paper7CRTEnvelope.reported_a_leaf_b_le_eighteen

end Paper7CRTEnvelope
