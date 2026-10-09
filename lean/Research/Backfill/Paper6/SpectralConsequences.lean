import Research.Backfill.Paper6.S0Witnesses
import Research.Backfill.Paper6.S0Comparison
import Research.Backfill.Paper6.P1

/-!
# Paper 6 V3: LA Proposition 4 and the exact Carlet equivalence

These proofs use the actual sparse polynomial witnesses exported by the full
S0Witnesses source. That source and its complete local dependency chain still
require actual validation. No assumption replaces its proof declarations here.

The LA domain is included in S0 using the accepted exact set comparison.
For Carlet's equivalence, the middle interval outside U is in S0 by its
definition, while U is U0 together with its complement image. P1 supplies the
actual complementary codewords. The four unknown weights remain exactly the
hypothesis of the reverse implication, never asserted unconditionally.

Frozen FROZEN.json SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
Source candidates only; root controls compilation and acceptance of the full chain.
-/

set_option autoImplicit false

namespace Paper6SpectralConsequences

open BackfillPaper6.V3

/-- Extract an actual RM word from the complete sparse-polynomial witness interface. -/
theorem isWeight_of_mem_S0 (w : ℕ) (hw : w ∈ S0) : IsWeight 7 14 w := by
  obtain ⟨p, hp, _hsupport, hweight⟩ := Paper6S0Witnesses.check_ThmB_witnesses w hw
  exact ⟨evalFun p, ⟨p, hp, rfl⟩, hweight⟩

/-- Preserve the whole LA domain, including the upper bound in the natural complement clause. -/
theorem la_entry_mem_S0 (w : ℕ)
    (hbase : w ∈ W0 ∨ (Even w ∧ 312 ≤ w ∧ w ≤ 16384 - 312) ∨
      (w ≤ 16384 ∧ 16384 - w ∈ W0))
    (hnot : w ∉ M) : w ∈ S0 := by
  change w ∈ (S0 : Set ℕ)
  rw [Paper6FiniteFacts.check_S0_eq_LA]
  exact Or.inl ⟨hbase, hnot⟩

/-- The exact frozen LA proposition, with its full unbounded natural-number quantifier. -/
theorem laProp4 : BackfillPaper6.V3.LAProp4 := by
  intro w hbase hnot
  exact isWeight_of_mem_S0 w (la_entry_mem_S0 w hbase hnot)

/-- Only four displayed numbers are checked here, not the full interval. -/
theorem u0_interval : ∀ w ∈ U0, Even w ∧ 320 ≤ w ∧ w ≤ 16064 := by
  decide +kernel

/-- The eight excluded weights are the four low weights and their four complements. -/
theorem u_decomposition : U = U0 ∪ U0.image (fun w => 16384 - w) := by
  decide +kernel

/-- If the four unknown low weights are attained, P1 supplies every member of U. -/
theorem isWeight_of_mem_U (hU0 : ∀ w ∈ U0, IsWeight 7 14 w)
    (w : ℕ) (hw : w ∈ U) : IsWeight 7 14 w := by
  rw [u_decomposition] at hw
  rcases Finset.mem_union.mp hw with hlow | hhigh
  · exact hU0 w hlow
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hhigh
    simpa only [show (2 : ℕ) ^ 14 = 16384 from by norm_num] using
      (Paper6Parity.complement_weight 7 14 k (hU0 k hk)).2

/-- Interval membership is proved symbolically, with no finite enumeration of the interval. -/
theorem mem_S0_of_even_interval (w : ℕ) (heven : Even w)
    (hlow : 320 ≤ w) (hhigh : w ≤ 16064) (hnot : w ∉ U) : w ∈ S0 := by
  unfold S0
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, hnot⟩
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (by omega), hlow, heven⟩

/-- The exact frozen equivalence, retaining both implications and all four unknown weights. -/
theorem carletEquiv : BackfillPaper6.V3.CarletEquiv := by
  constructor
  · intro hCarlet w hw
    have hinterval := u0_interval w hw
    exact hCarlet w hinterval.1 hinterval.2.1 hinterval.2.2
  · intro hU0 w heven hlow hhigh
    by_cases hwU : w ∈ U
    · exact isWeight_of_mem_U hU0 w hwU
    · exact isWeight_of_mem_S0 w (mem_S0_of_even_interval w heven hlow hhigh hwU)

/-- Exact frozen LA contract check; the alias does not add a result. -/
theorem check_LAProp4 : BackfillPaper6.V3.LAProp4 := laProp4

/-- Exact frozen Carlet contract check; the alias does not assert CarletQ714 itself. -/
theorem check_CarletEquiv : BackfillPaper6.V3.CarletEquiv := carletEquiv

end Paper6SpectralConsequences

#print axioms Paper6SpectralConsequences.isWeight_of_mem_S0
#print axioms Paper6SpectralConsequences.la_entry_mem_S0
#print axioms Paper6SpectralConsequences.laProp4
#print axioms Paper6SpectralConsequences.u0_interval
#print axioms Paper6SpectralConsequences.u_decomposition
#print axioms Paper6SpectralConsequences.isWeight_of_mem_U
#print axioms Paper6SpectralConsequences.mem_S0_of_even_interval
#print axioms Paper6SpectralConsequences.carletEquiv
#print axioms Paper6SpectralConsequences.check_LAProp4
#print axioms Paper6SpectralConsequences.check_CarletEquiv
#print Paper6SpectralConsequences.check_LAProp4
#print Paper6SpectralConsequences.check_CarletEquiv
