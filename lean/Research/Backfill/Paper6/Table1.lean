import Research.Backfill.Paper6.ChallengeV3
import Research.Backfill.Paper6.InclusionExclusion
import Research.Backfill.Paper6.P1

/-!
# Paper 6 V3: the complete concrete Table 1

The ten actual frozen monomial lists are checked, including distinctness, all
monomial degrees, every sigma entry and the signed sigma sums. Their Hamming
weights follow from the general accepted inclusion-exclusion theorem applied
to the evaluation of these exact polynomials. Each finite weight computation
has at most 63 nonempty subsets of a family of at most six monomials; it does
not enumerate all 16384 evaluation points. The seven complement assertions
then follow from the accepted general binary complement-weight identity.

Frozen FROZEN.json SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
Source candidate only. All compilation and acceptance are root-controlled.
-/

set_option autoImplicit false

namespace Paper6TableOne

open BackfillPaper6.V3

/-- Evaluating a list polynomial is summing its indexed monomial evaluations. -/
theorem evalFun_polyOf_eq_sum {m : ℕ} (Ls : List (Finset (Fin m))) :
    evalFun (polyOf Ls) =
      fun x : Pt m => ∑ i : Fin Ls.length, ∏ j ∈ Ls.get i, x j := by
  classical
  funext x
  calc
    evalFun (polyOf Ls) x = (Ls.map fun S => ∏ j ∈ S, x j).sum := by
      simp only [evalFun, polyOf, map_list_sum, List.map_map, Function.comp_def,
        MvPolynomial.eval_prod, MvPolynomial.eval_X]
    _ = (List.ofFn (fun i : Fin Ls.length => ∏ j ∈ Ls.get i, x j)).sum := by
      have hmap := List.ofFn_comp' Ls.get
        (fun S : Finset (Fin m) => ∏ j ∈ S, x j)
      rw [List.ofFn_get] at hmap
      exact congrArg (fun values : List (ZMod 2) => values.sum) hmap.symm
    _ = ∑ i : Fin Ls.length, ∏ j ∈ Ls.get i, x j := Fin.sum_ofFn _

/-- The exact finite inclusion-exclusion expression for a frozen monomial list. -/
def inclusionSum (Ls : List (Finset (Fin 14))) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Fin Ls.length))).filter (fun T => T.Nonempty),
    (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^ (14 - (T.biUnion fun i => Ls.get i).card)

/-- The finite sum computes the Hamming weight of the actual list polynomial. -/
theorem hammingNorm_polyOf_eq_inclusionSum (Ls : List (Finset (Fin 14))) :
    (hammingNorm (evalFun (polyOf Ls)) : ℤ) = inclusionSum Ls := by
  rw [evalFun_polyOf_eq_sum]
  exact Paper6InclusionExclusion.check_Lem21 14 Ls.length Ls.get

/-- All finite data required for one concrete row, including its actual subset sum. -/
def RowData (t : ℕ × List (Finset (Fin 14))) : Prop :=
  t.2.Nodup ∧
  (∀ S ∈ t.2, S.card ≤ 7) ∧
  inclusionSum t.2 = (t.1 : ℤ) ∧
  (∀ s ∈ table1Sigma, t.1 = s.1 →
    s.2.length = t.2.length ∧
    (∀ j : Fin s.2.length, s.2.get j = sigma t.2 (j.val + 1)) ∧
    (t.1 : ℤ) = ∑ j : Fin s.2.length, (-2 : ℤ) ^ j.val * (s.2.get j : ℤ))

/-! ### Bounded row certificates

Development 02 exhausted one 200000-heartbeat declaration containing every row.
Each calculation below checks only one structural fact, inclusion sum, or sigma
entry. Each declaration retains the same finite heartbeat bound. The recursion
bound 8192 is retained from Development 01, scoped to that one certificate.
The final universal theorem performs only finite case assembly.
-/

/-- Frozen row 1, printed weight 354; no monomial data are copied. -/
abbrev row_01 : ℕ × List (Finset (Fin 14)) := table1.get ⟨0, by decide⟩

abbrev sigmaRow_01 : ℕ × List ℕ := table1Sigma.get ⟨0, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_01_structure :
    row_01.2.Nodup ∧ (∀ S ∈ row_01.2, S.card ≤ 7) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_01_inclusion :
    inclusionSum row_01.2 = (row_01.1 : ℤ) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_01_length :
    sigmaRow_01.2.length = row_01.2.length := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_01_sigma_select :
    ∀ s ∈ table1Sigma, row_01.1 = s.1 → s = sigmaRow_01 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_01_sigma_01 :
    sigma row_01.2 1 = sigmaRow_01.2.get ⟨0, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_01_sigma_02 :
    sigma row_01.2 2 = sigmaRow_01.2.get ⟨1, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_01_sigma_03 :
    sigma row_01.2 3 = sigmaRow_01.2.get ⟨2, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_01_sigma_04 :
    sigma row_01.2 4 = sigmaRow_01.2.get ⟨3, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_01_sigma_05 :
    sigma row_01.2 5 = sigmaRow_01.2.get ⟨4, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_01_signed :
    (row_01.1 : ℤ) = ∑ j : Fin sigmaRow_01.2.length,
      (-2 : ℤ) ^ j.val * (sigmaRow_01.2.get j : ℤ) := by
  decide +kernel

theorem row_01_sigma_values :
    ∀ j : Fin sigmaRow_01.2.length, sigmaRow_01.2.get j = sigma row_01.2 (j.val + 1) := by
  intro j
  fin_cases j
  · exact row_01_sigma_01.symm
  · exact row_01_sigma_02.symm
  · exact row_01_sigma_03.symm
  · exact row_01_sigma_04.symm
  · exact row_01_sigma_05.symm

theorem row_01_data : RowData row_01 := by
  refine ⟨row_01_structure.1, row_01_structure.2, row_01_inclusion, ?_⟩
  intro s hs hweight
  have hmatch := row_01_sigma_select s hs hweight
  subst s
  exact ⟨row_01_length, row_01_sigma_values, row_01_signed⟩

/-- Frozen row 2, printed weight 4378; no monomial data are copied. -/
abbrev row_02 : ℕ × List (Finset (Fin 14)) := table1.get ⟨1, by decide⟩

abbrev sigmaRow_02 : ℕ × List ℕ := table1Sigma.get ⟨1, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_02_structure :
    row_02.2.Nodup ∧ (∀ S ∈ row_02.2, S.card ≤ 7) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_02_inclusion :
    inclusionSum row_02.2 = (row_02.1 : ℤ) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_02_length :
    sigmaRow_02.2.length = row_02.2.length := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_02_sigma_select :
    ∀ s ∈ table1Sigma, row_02.1 = s.1 → s = sigmaRow_02 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_02_sigma_01 :
    sigma row_02.2 1 = sigmaRow_02.2.get ⟨0, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_02_sigma_02 :
    sigma row_02.2 2 = sigmaRow_02.2.get ⟨1, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_02_sigma_03 :
    sigma row_02.2 3 = sigmaRow_02.2.get ⟨2, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_02_sigma_04 :
    sigma row_02.2 4 = sigmaRow_02.2.get ⟨3, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_02_sigma_05 :
    sigma row_02.2 5 = sigmaRow_02.2.get ⟨4, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_02_signed :
    (row_02.1 : ℤ) = ∑ j : Fin sigmaRow_02.2.length,
      (-2 : ℤ) ^ j.val * (sigmaRow_02.2.get j : ℤ) := by
  decide +kernel

theorem row_02_sigma_values :
    ∀ j : Fin sigmaRow_02.2.length, sigmaRow_02.2.get j = sigma row_02.2 (j.val + 1) := by
  intro j
  fin_cases j
  · exact row_02_sigma_01.symm
  · exact row_02_sigma_02.symm
  · exact row_02_sigma_03.symm
  · exact row_02_sigma_04.symm
  · exact row_02_sigma_05.symm

theorem row_02_data : RowData row_02 := by
  refine ⟨row_02_structure.1, row_02_structure.2, row_02_inclusion, ?_⟩
  intro s hs hweight
  have hmatch := row_02_sigma_select s hs hweight
  subst s
  exact ⟨row_02_length, row_02_sigma_values, row_02_signed⟩

/-- Frozen row 3, printed weight 4380; no monomial data are copied. -/
abbrev row_03 : ℕ × List (Finset (Fin 14)) := table1.get ⟨2, by decide⟩

abbrev sigmaRow_03 : ℕ × List ℕ := table1Sigma.get ⟨2, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_03_structure :
    row_03.2.Nodup ∧ (∀ S ∈ row_03.2, S.card ≤ 7) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_03_inclusion :
    inclusionSum row_03.2 = (row_03.1 : ℤ) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_03_length :
    sigmaRow_03.2.length = row_03.2.length := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_03_sigma_select :
    ∀ s ∈ table1Sigma, row_03.1 = s.1 → s = sigmaRow_03 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_03_sigma_01 :
    sigma row_03.2 1 = sigmaRow_03.2.get ⟨0, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_03_sigma_02 :
    sigma row_03.2 2 = sigmaRow_03.2.get ⟨1, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_03_sigma_03 :
    sigma row_03.2 3 = sigmaRow_03.2.get ⟨2, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_03_sigma_04 :
    sigma row_03.2 4 = sigmaRow_03.2.get ⟨3, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_03_signed :
    (row_03.1 : ℤ) = ∑ j : Fin sigmaRow_03.2.length,
      (-2 : ℤ) ^ j.val * (sigmaRow_03.2.get j : ℤ) := by
  decide +kernel

theorem row_03_sigma_values :
    ∀ j : Fin sigmaRow_03.2.length, sigmaRow_03.2.get j = sigma row_03.2 (j.val + 1) := by
  intro j
  fin_cases j
  · exact row_03_sigma_01.symm
  · exact row_03_sigma_02.symm
  · exact row_03_sigma_03.symm
  · exact row_03_sigma_04.symm

theorem row_03_data : RowData row_03 := by
  refine ⟨row_03_structure.1, row_03_structure.2, row_03_inclusion, ?_⟩
  intro s hs hweight
  have hmatch := row_03_sigma_select s hs hweight
  subst s
  exact ⟨row_03_length, row_03_sigma_values, row_03_signed⟩

/-- Frozen row 4, printed weight 4382; no monomial data are copied. -/
abbrev row_04 : ℕ × List (Finset (Fin 14)) := table1.get ⟨3, by decide⟩

abbrev sigmaRow_04 : ℕ × List ℕ := table1Sigma.get ⟨3, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_04_structure :
    row_04.2.Nodup ∧ (∀ S ∈ row_04.2, S.card ≤ 7) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_04_inclusion :
    inclusionSum row_04.2 = (row_04.1 : ℤ) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_04_length :
    sigmaRow_04.2.length = row_04.2.length := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_04_sigma_select :
    ∀ s ∈ table1Sigma, row_04.1 = s.1 → s = sigmaRow_04 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_04_sigma_01 :
    sigma row_04.2 1 = sigmaRow_04.2.get ⟨0, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_04_sigma_02 :
    sigma row_04.2 2 = sigmaRow_04.2.get ⟨1, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_04_sigma_03 :
    sigma row_04.2 3 = sigmaRow_04.2.get ⟨2, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_04_sigma_04 :
    sigma row_04.2 4 = sigmaRow_04.2.get ⟨3, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_04_sigma_05 :
    sigma row_04.2 5 = sigmaRow_04.2.get ⟨4, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_04_signed :
    (row_04.1 : ℤ) = ∑ j : Fin sigmaRow_04.2.length,
      (-2 : ℤ) ^ j.val * (sigmaRow_04.2.get j : ℤ) := by
  decide +kernel

theorem row_04_sigma_values :
    ∀ j : Fin sigmaRow_04.2.length, sigmaRow_04.2.get j = sigma row_04.2 (j.val + 1) := by
  intro j
  fin_cases j
  · exact row_04_sigma_01.symm
  · exact row_04_sigma_02.symm
  · exact row_04_sigma_03.symm
  · exact row_04_sigma_04.symm
  · exact row_04_sigma_05.symm

theorem row_04_data : RowData row_04 := by
  refine ⟨row_04_structure.1, row_04_structure.2, row_04_inclusion, ?_⟩
  intro s hs hweight
  have hmatch := row_04_sigma_select s hs hweight
  subst s
  exact ⟨row_04_length, row_04_sigma_values, row_04_signed⟩

/-- Frozen row 5, printed weight 8174; no monomial data are copied. -/
abbrev row_05 : ℕ × List (Finset (Fin 14)) := table1.get ⟨4, by decide⟩

abbrev sigmaRow_05 : ℕ × List ℕ := table1Sigma.get ⟨4, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_05_structure :
    row_05.2.Nodup ∧ (∀ S ∈ row_05.2, S.card ≤ 7) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_05_inclusion :
    inclusionSum row_05.2 = (row_05.1 : ℤ) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_05_length :
    sigmaRow_05.2.length = row_05.2.length := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_05_sigma_select :
    ∀ s ∈ table1Sigma, row_05.1 = s.1 → s = sigmaRow_05 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_05_sigma_01 :
    sigma row_05.2 1 = sigmaRow_05.2.get ⟨0, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_05_sigma_02 :
    sigma row_05.2 2 = sigmaRow_05.2.get ⟨1, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_05_sigma_03 :
    sigma row_05.2 3 = sigmaRow_05.2.get ⟨2, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_05_sigma_04 :
    sigma row_05.2 4 = sigmaRow_05.2.get ⟨3, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_05_sigma_05 :
    sigma row_05.2 5 = sigmaRow_05.2.get ⟨4, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_05_sigma_06 :
    sigma row_05.2 6 = sigmaRow_05.2.get ⟨5, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_05_signed :
    (row_05.1 : ℤ) = ∑ j : Fin sigmaRow_05.2.length,
      (-2 : ℤ) ^ j.val * (sigmaRow_05.2.get j : ℤ) := by
  decide +kernel

theorem row_05_sigma_values :
    ∀ j : Fin sigmaRow_05.2.length, sigmaRow_05.2.get j = sigma row_05.2 (j.val + 1) := by
  intro j
  fin_cases j
  · exact row_05_sigma_01.symm
  · exact row_05_sigma_02.symm
  · exact row_05_sigma_03.symm
  · exact row_05_sigma_04.symm
  · exact row_05_sigma_05.symm
  · exact row_05_sigma_06.symm

theorem row_05_data : RowData row_05 := by
  refine ⟨row_05_structure.1, row_05_structure.2, row_05_inclusion, ?_⟩
  intro s hs hweight
  have hmatch := row_05_sigma_select s hs hweight
  subst s
  exact ⟨row_05_length, row_05_sigma_values, row_05_signed⟩

/-- Frozen row 6, printed weight 8178; no monomial data are copied. -/
abbrev row_06 : ℕ × List (Finset (Fin 14)) := table1.get ⟨5, by decide⟩

abbrev sigmaRow_06 : ℕ × List ℕ := table1Sigma.get ⟨5, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_06_structure :
    row_06.2.Nodup ∧ (∀ S ∈ row_06.2, S.card ≤ 7) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_06_inclusion :
    inclusionSum row_06.2 = (row_06.1 : ℤ) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_06_length :
    sigmaRow_06.2.length = row_06.2.length := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_06_sigma_select :
    ∀ s ∈ table1Sigma, row_06.1 = s.1 → s = sigmaRow_06 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_06_sigma_01 :
    sigma row_06.2 1 = sigmaRow_06.2.get ⟨0, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_06_sigma_02 :
    sigma row_06.2 2 = sigmaRow_06.2.get ⟨1, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_06_sigma_03 :
    sigma row_06.2 3 = sigmaRow_06.2.get ⟨2, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_06_sigma_04 :
    sigma row_06.2 4 = sigmaRow_06.2.get ⟨3, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_06_sigma_05 :
    sigma row_06.2 5 = sigmaRow_06.2.get ⟨4, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_06_signed :
    (row_06.1 : ℤ) = ∑ j : Fin sigmaRow_06.2.length,
      (-2 : ℤ) ^ j.val * (sigmaRow_06.2.get j : ℤ) := by
  decide +kernel

theorem row_06_sigma_values :
    ∀ j : Fin sigmaRow_06.2.length, sigmaRow_06.2.get j = sigma row_06.2 (j.val + 1) := by
  intro j
  fin_cases j
  · exact row_06_sigma_01.symm
  · exact row_06_sigma_02.symm
  · exact row_06_sigma_03.symm
  · exact row_06_sigma_04.symm
  · exact row_06_sigma_05.symm

theorem row_06_data : RowData row_06 := by
  refine ⟨row_06_structure.1, row_06_structure.2, row_06_inclusion, ?_⟩
  intro s hs hweight
  have hmatch := row_06_sigma_select s hs hweight
  subst s
  exact ⟨row_06_length, row_06_sigma_values, row_06_signed⟩

/-- Frozen row 7, printed weight 8182; no monomial data are copied. -/
abbrev row_07 : ℕ × List (Finset (Fin 14)) := table1.get ⟨6, by decide⟩

abbrev sigmaRow_07 : ℕ × List ℕ := table1Sigma.get ⟨6, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_07_structure :
    row_07.2.Nodup ∧ (∀ S ∈ row_07.2, S.card ≤ 7) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_07_inclusion :
    inclusionSum row_07.2 = (row_07.1 : ℤ) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_07_length :
    sigmaRow_07.2.length = row_07.2.length := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_07_sigma_select :
    ∀ s ∈ table1Sigma, row_07.1 = s.1 → s = sigmaRow_07 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_07_sigma_01 :
    sigma row_07.2 1 = sigmaRow_07.2.get ⟨0, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_07_sigma_02 :
    sigma row_07.2 2 = sigmaRow_07.2.get ⟨1, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_07_sigma_03 :
    sigma row_07.2 3 = sigmaRow_07.2.get ⟨2, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_07_sigma_04 :
    sigma row_07.2 4 = sigmaRow_07.2.get ⟨3, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_07_sigma_05 :
    sigma row_07.2 5 = sigmaRow_07.2.get ⟨4, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_07_sigma_06 :
    sigma row_07.2 6 = sigmaRow_07.2.get ⟨5, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_07_signed :
    (row_07.1 : ℤ) = ∑ j : Fin sigmaRow_07.2.length,
      (-2 : ℤ) ^ j.val * (sigmaRow_07.2.get j : ℤ) := by
  decide +kernel

theorem row_07_sigma_values :
    ∀ j : Fin sigmaRow_07.2.length, sigmaRow_07.2.get j = sigma row_07.2 (j.val + 1) := by
  intro j
  fin_cases j
  · exact row_07_sigma_01.symm
  · exact row_07_sigma_02.symm
  · exact row_07_sigma_03.symm
  · exact row_07_sigma_04.symm
  · exact row_07_sigma_05.symm
  · exact row_07_sigma_06.symm

theorem row_07_data : RowData row_07 := by
  refine ⟨row_07_structure.1, row_07_structure.2, row_07_inclusion, ?_⟩
  intro s hs hweight
  have hmatch := row_07_sigma_select s hs hweight
  subst s
  exact ⟨row_07_length, row_07_sigma_values, row_07_signed⟩

/-- Frozen row 8, printed weight 8186; no monomial data are copied. -/
abbrev row_08 : ℕ × List (Finset (Fin 14)) := table1.get ⟨7, by decide⟩

abbrev sigmaRow_08 : ℕ × List ℕ := table1Sigma.get ⟨7, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_08_structure :
    row_08.2.Nodup ∧ (∀ S ∈ row_08.2, S.card ≤ 7) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_08_inclusion :
    inclusionSum row_08.2 = (row_08.1 : ℤ) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_08_length :
    sigmaRow_08.2.length = row_08.2.length := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_08_sigma_select :
    ∀ s ∈ table1Sigma, row_08.1 = s.1 → s = sigmaRow_08 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_08_sigma_01 :
    sigma row_08.2 1 = sigmaRow_08.2.get ⟨0, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_08_sigma_02 :
    sigma row_08.2 2 = sigmaRow_08.2.get ⟨1, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_08_sigma_03 :
    sigma row_08.2 3 = sigmaRow_08.2.get ⟨2, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_08_sigma_04 :
    sigma row_08.2 4 = sigmaRow_08.2.get ⟨3, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_08_sigma_05 :
    sigma row_08.2 5 = sigmaRow_08.2.get ⟨4, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_08_signed :
    (row_08.1 : ℤ) = ∑ j : Fin sigmaRow_08.2.length,
      (-2 : ℤ) ^ j.val * (sigmaRow_08.2.get j : ℤ) := by
  decide +kernel

theorem row_08_sigma_values :
    ∀ j : Fin sigmaRow_08.2.length, sigmaRow_08.2.get j = sigma row_08.2 (j.val + 1) := by
  intro j
  fin_cases j
  · exact row_08_sigma_01.symm
  · exact row_08_sigma_02.symm
  · exact row_08_sigma_03.symm
  · exact row_08_sigma_04.symm
  · exact row_08_sigma_05.symm

theorem row_08_data : RowData row_08 := by
  refine ⟨row_08_structure.1, row_08_structure.2, row_08_inclusion, ?_⟩
  intro s hs hweight
  have hmatch := row_08_sigma_select s hs hweight
  subst s
  exact ⟨row_08_length, row_08_sigma_values, row_08_signed⟩

/-- Frozen row 9, printed weight 8188; no monomial data are copied. -/
abbrev row_09 : ℕ × List (Finset (Fin 14)) := table1.get ⟨8, by decide⟩

abbrev sigmaRow_09 : ℕ × List ℕ := table1Sigma.get ⟨8, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_09_structure :
    row_09.2.Nodup ∧ (∀ S ∈ row_09.2, S.card ≤ 7) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_09_inclusion :
    inclusionSum row_09.2 = (row_09.1 : ℤ) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_09_length :
    sigmaRow_09.2.length = row_09.2.length := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_09_sigma_select :
    ∀ s ∈ table1Sigma, row_09.1 = s.1 → s = sigmaRow_09 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_09_sigma_01 :
    sigma row_09.2 1 = sigmaRow_09.2.get ⟨0, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_09_sigma_02 :
    sigma row_09.2 2 = sigmaRow_09.2.get ⟨1, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_09_sigma_03 :
    sigma row_09.2 3 = sigmaRow_09.2.get ⟨2, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_09_sigma_04 :
    sigma row_09.2 4 = sigmaRow_09.2.get ⟨3, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_09_signed :
    (row_09.1 : ℤ) = ∑ j : Fin sigmaRow_09.2.length,
      (-2 : ℤ) ^ j.val * (sigmaRow_09.2.get j : ℤ) := by
  decide +kernel

theorem row_09_sigma_values :
    ∀ j : Fin sigmaRow_09.2.length, sigmaRow_09.2.get j = sigma row_09.2 (j.val + 1) := by
  intro j
  fin_cases j
  · exact row_09_sigma_01.symm
  · exact row_09_sigma_02.symm
  · exact row_09_sigma_03.symm
  · exact row_09_sigma_04.symm

theorem row_09_data : RowData row_09 := by
  refine ⟨row_09_structure.1, row_09_structure.2, row_09_inclusion, ?_⟩
  intro s hs hweight
  have hmatch := row_09_sigma_select s hs hweight
  subst s
  exact ⟨row_09_length, row_09_sigma_values, row_09_signed⟩

/-- Frozen row 10, printed weight 8190; no monomial data are copied. -/
abbrev row_10 : ℕ × List (Finset (Fin 14)) := table1.get ⟨9, by decide⟩

abbrev sigmaRow_10 : ℕ × List ℕ := table1Sigma.get ⟨9, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_10_structure :
    row_10.2.Nodup ∧ (∀ S ∈ row_10.2, S.card ≤ 7) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_10_inclusion :
    inclusionSum row_10.2 = (row_10.1 : ℤ) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_10_length :
    sigmaRow_10.2.length = row_10.2.length := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_10_sigma_select :
    ∀ s ∈ table1Sigma, row_10.1 = s.1 → s = sigmaRow_10 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_10_sigma_01 :
    sigma row_10.2 1 = sigmaRow_10.2.get ⟨0, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_10_sigma_02 :
    sigma row_10.2 2 = sigmaRow_10.2.get ⟨1, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_10_sigma_03 :
    sigma row_10.2 3 = sigmaRow_10.2.get ⟨2, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_10_sigma_04 :
    sigma row_10.2 4 = sigmaRow_10.2.get ⟨3, by decide⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 200000 in
theorem row_10_signed :
    (row_10.1 : ℤ) = ∑ j : Fin sigmaRow_10.2.length,
      (-2 : ℤ) ^ j.val * (sigmaRow_10.2.get j : ℤ) := by
  decide +kernel

theorem row_10_sigma_values :
    ∀ j : Fin sigmaRow_10.2.length, sigmaRow_10.2.get j = sigma row_10.2 (j.val + 1) := by
  intro j
  fin_cases j
  · exact row_10_sigma_01.symm
  · exact row_10_sigma_02.symm
  · exact row_10_sigma_03.symm
  · exact row_10_sigma_04.symm

theorem row_10_data : RowData row_10 := by
  refine ⟨row_10_structure.1, row_10_structure.2, row_10_inclusion, ?_⟩
  intro s hs hweight
  have hmatch := row_10_sigma_select s hs hweight
  subst s
  exact ⟨row_10_length, row_10_sigma_values, row_10_signed⟩

/-- Assemble ten separately proved rows; no combined arithmetic decision remains. -/
theorem all_row_data : ∀ t ∈ table1, RowData t := by
  intro t ht
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ht
  rw [← hi]
  fin_cases i
  · exact row_01_data
  · exact row_02_data
  · exact row_03_data
  · exact row_04_data
  · exact row_05_data
  · exact row_06_data
  · exact row_07_data
  · exact row_08_data
  · exact row_09_data
  · exact row_10_data

/-- Every row has its printed weight and every entry of its printed sigma column. -/
theorem table_rows (w : ℕ) (Ls : List (Finset (Fin 14))) (hrow : (w, Ls) ∈ table1) :
    Ls.Nodup ∧ (∀ S ∈ Ls, S.card ≤ 7) ∧ hammingNorm (evalFun (polyOf Ls)) = w ∧
      (∀ σ, (w, σ) ∈ table1Sigma →
        σ.length = Ls.length ∧ (∀ j : Fin σ.length, σ.get j = sigma Ls (j.val + 1)) ∧
        (w : ℤ) = ∑ j : Fin σ.length, (-2 : ℤ) ^ j.val * (σ.get j : ℤ)) := by
  have hd := all_row_data (w, Ls) hrow
  refine ⟨hd.1, hd.2.1, ?_, ?_⟩
  · have hw : (hammingNorm (evalFun (polyOf Ls)) : ℤ) = (w : ℤ) :=
      (hammingNorm_polyOf_eq_inclusionSum Ls).trans hd.2.2.1
    exact_mod_cast hw
  · intro σ hσ
    exact hd.2.2.2 (w, σ) hσ rfl

/-- A product of distinct coordinate variables has degree at most its cardinality. -/
theorem monomial_degree_le {m : ℕ} (S : Finset (Fin m)) :
    (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin m) (ZMod 2))).totalDegree ≤ S.card := by
  classical
  simpa using MvPolynomial.totalDegree_finsetProd S
    (fun i => (MvPolynomial.X i : MvPolynomial (Fin m) (ZMod 2)))

/-- A monomial list with a common degree bound defines a polynomial with that bound. -/
theorem polyOf_degree_le {m : ℕ} (Ls : List (Finset (Fin m))) (r : ℕ) :
    (∀ S ∈ Ls, S.card ≤ r) → (polyOf Ls).totalDegree ≤ r := by
  induction Ls with
  | nil =>
      intro h
      simp [polyOf]
  | cons S Ls ih =>
      intro h
      change ((∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin m) (ZMod 2))) +
        polyOf Ls).totalDegree ≤ r
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le ((monomial_degree_le S).trans (h S List.mem_cons_self))
          (ih (fun T hT => h T (List.mem_cons_of_mem S hT))))

/-- The exact polynomial printed in each row has degree at most seven and lies in RM(7,14). -/
theorem table_row_polynomial (w : ℕ) (Ls : List (Finset (Fin 14)))
    (hrow : (w, Ls) ∈ table1) :
    (polyOf Ls).totalDegree ≤ 7 ∧ evalFun (polyOf Ls) ∈ RM 7 14 := by
  have hp := polyOf_degree_le Ls 7 (table_rows w Ls hrow).2.1
  exact ⟨hp, polyOf Ls, hp, rfl⟩

/-- Adding the constant polynomial one complements the actual evaluation function. -/
theorem evalFun_one_add_polyOf (Ls : List (Finset (Fin 14))) :
    evalFun (1 + polyOf Ls) = evalFun (polyOf Ls) + 1 := by
  funext x
  change MvPolynomial.eval x (1 + polyOf Ls) = MvPolynomial.eval x (polyOf Ls) + 1
  rw [map_add, map_one, add_comm]

/-- The seven printed pairs have exactly complementary numerical weights. -/
theorem complement_numbers :
    ∀ t ∈ ([(354, 16030), (8190, 8194), (8188, 8196), (8186, 8198),
      (8182, 8202), (8178, 8206), (8174, 8210)] : List (ℕ × ℕ)), 16384 - t.1 = t.2 := by
  decide +kernel

/-- Every specified complement is the complement of the exact frozen row polynomial. -/
theorem table_complements (w w' : ℕ) (Ls : List (Finset (Fin 14)))
    (hpair : (w, w') ∈ [(354, 16030), (8190, 8194), (8188, 8196), (8186, 8198),
      (8182, 8202), (8178, 8206), (8174, 8210)])
    (hrow : (w, Ls) ∈ table1) : hammingNorm (evalFun (1 + polyOf Ls)) = w' := by
  rw [evalFun_one_add_polyOf, Paper6Parity.hammingNorm_add_one,
    (table_rows w Ls hrow).2.2.1]
  change 16384 - w = w'
  exact complement_numbers (w, w') hpair

/-- The whole unchanged frozen Table 1 contract, including the seven complements. -/
theorem table1_complete : BackfillPaper6.V3.Table1 := by
  exact ⟨table_rows, table_complements⟩

/-- Exact frozen contract check; the alias is not a second mathematical result. -/
theorem check_Table1 : BackfillPaper6.V3.Table1 := table1_complete

end Paper6TableOne

#print axioms Paper6TableOne.evalFun_polyOf_eq_sum
#print axioms Paper6TableOne.inclusionSum
#print axioms Paper6TableOne.hammingNorm_polyOf_eq_inclusionSum
#print axioms Paper6TableOne.RowData
#print axioms Paper6TableOne.row_01
#print axioms Paper6TableOne.sigmaRow_01
#print axioms Paper6TableOne.row_01_structure
#print axioms Paper6TableOne.row_01_inclusion
#print axioms Paper6TableOne.row_01_length
#print axioms Paper6TableOne.row_01_sigma_select
#print axioms Paper6TableOne.row_01_sigma_01
#print axioms Paper6TableOne.row_01_sigma_02
#print axioms Paper6TableOne.row_01_sigma_03
#print axioms Paper6TableOne.row_01_sigma_04
#print axioms Paper6TableOne.row_01_sigma_05
#print axioms Paper6TableOne.row_01_signed
#print axioms Paper6TableOne.row_01_sigma_values
#print axioms Paper6TableOne.row_01_data
#print axioms Paper6TableOne.row_02
#print axioms Paper6TableOne.sigmaRow_02
#print axioms Paper6TableOne.row_02_structure
#print axioms Paper6TableOne.row_02_inclusion
#print axioms Paper6TableOne.row_02_length
#print axioms Paper6TableOne.row_02_sigma_select
#print axioms Paper6TableOne.row_02_sigma_01
#print axioms Paper6TableOne.row_02_sigma_02
#print axioms Paper6TableOne.row_02_sigma_03
#print axioms Paper6TableOne.row_02_sigma_04
#print axioms Paper6TableOne.row_02_sigma_05
#print axioms Paper6TableOne.row_02_signed
#print axioms Paper6TableOne.row_02_sigma_values
#print axioms Paper6TableOne.row_02_data
#print axioms Paper6TableOne.row_03
#print axioms Paper6TableOne.sigmaRow_03
#print axioms Paper6TableOne.row_03_structure
#print axioms Paper6TableOne.row_03_inclusion
#print axioms Paper6TableOne.row_03_length
#print axioms Paper6TableOne.row_03_sigma_select
#print axioms Paper6TableOne.row_03_sigma_01
#print axioms Paper6TableOne.row_03_sigma_02
#print axioms Paper6TableOne.row_03_sigma_03
#print axioms Paper6TableOne.row_03_sigma_04
#print axioms Paper6TableOne.row_03_signed
#print axioms Paper6TableOne.row_03_sigma_values
#print axioms Paper6TableOne.row_03_data
#print axioms Paper6TableOne.row_04
#print axioms Paper6TableOne.sigmaRow_04
#print axioms Paper6TableOne.row_04_structure
#print axioms Paper6TableOne.row_04_inclusion
#print axioms Paper6TableOne.row_04_length
#print axioms Paper6TableOne.row_04_sigma_select
#print axioms Paper6TableOne.row_04_sigma_01
#print axioms Paper6TableOne.row_04_sigma_02
#print axioms Paper6TableOne.row_04_sigma_03
#print axioms Paper6TableOne.row_04_sigma_04
#print axioms Paper6TableOne.row_04_sigma_05
#print axioms Paper6TableOne.row_04_signed
#print axioms Paper6TableOne.row_04_sigma_values
#print axioms Paper6TableOne.row_04_data
#print axioms Paper6TableOne.row_05
#print axioms Paper6TableOne.sigmaRow_05
#print axioms Paper6TableOne.row_05_structure
#print axioms Paper6TableOne.row_05_inclusion
#print axioms Paper6TableOne.row_05_length
#print axioms Paper6TableOne.row_05_sigma_select
#print axioms Paper6TableOne.row_05_sigma_01
#print axioms Paper6TableOne.row_05_sigma_02
#print axioms Paper6TableOne.row_05_sigma_03
#print axioms Paper6TableOne.row_05_sigma_04
#print axioms Paper6TableOne.row_05_sigma_05
#print axioms Paper6TableOne.row_05_sigma_06
#print axioms Paper6TableOne.row_05_signed
#print axioms Paper6TableOne.row_05_sigma_values
#print axioms Paper6TableOne.row_05_data
#print axioms Paper6TableOne.row_06
#print axioms Paper6TableOne.sigmaRow_06
#print axioms Paper6TableOne.row_06_structure
#print axioms Paper6TableOne.row_06_inclusion
#print axioms Paper6TableOne.row_06_length
#print axioms Paper6TableOne.row_06_sigma_select
#print axioms Paper6TableOne.row_06_sigma_01
#print axioms Paper6TableOne.row_06_sigma_02
#print axioms Paper6TableOne.row_06_sigma_03
#print axioms Paper6TableOne.row_06_sigma_04
#print axioms Paper6TableOne.row_06_sigma_05
#print axioms Paper6TableOne.row_06_signed
#print axioms Paper6TableOne.row_06_sigma_values
#print axioms Paper6TableOne.row_06_data
#print axioms Paper6TableOne.row_07
#print axioms Paper6TableOne.sigmaRow_07
#print axioms Paper6TableOne.row_07_structure
#print axioms Paper6TableOne.row_07_inclusion
#print axioms Paper6TableOne.row_07_length
#print axioms Paper6TableOne.row_07_sigma_select
#print axioms Paper6TableOne.row_07_sigma_01
#print axioms Paper6TableOne.row_07_sigma_02
#print axioms Paper6TableOne.row_07_sigma_03
#print axioms Paper6TableOne.row_07_sigma_04
#print axioms Paper6TableOne.row_07_sigma_05
#print axioms Paper6TableOne.row_07_sigma_06
#print axioms Paper6TableOne.row_07_signed
#print axioms Paper6TableOne.row_07_sigma_values
#print axioms Paper6TableOne.row_07_data
#print axioms Paper6TableOne.row_08
#print axioms Paper6TableOne.sigmaRow_08
#print axioms Paper6TableOne.row_08_structure
#print axioms Paper6TableOne.row_08_inclusion
#print axioms Paper6TableOne.row_08_length
#print axioms Paper6TableOne.row_08_sigma_select
#print axioms Paper6TableOne.row_08_sigma_01
#print axioms Paper6TableOne.row_08_sigma_02
#print axioms Paper6TableOne.row_08_sigma_03
#print axioms Paper6TableOne.row_08_sigma_04
#print axioms Paper6TableOne.row_08_sigma_05
#print axioms Paper6TableOne.row_08_signed
#print axioms Paper6TableOne.row_08_sigma_values
#print axioms Paper6TableOne.row_08_data
#print axioms Paper6TableOne.row_09
#print axioms Paper6TableOne.sigmaRow_09
#print axioms Paper6TableOne.row_09_structure
#print axioms Paper6TableOne.row_09_inclusion
#print axioms Paper6TableOne.row_09_length
#print axioms Paper6TableOne.row_09_sigma_select
#print axioms Paper6TableOne.row_09_sigma_01
#print axioms Paper6TableOne.row_09_sigma_02
#print axioms Paper6TableOne.row_09_sigma_03
#print axioms Paper6TableOne.row_09_sigma_04
#print axioms Paper6TableOne.row_09_signed
#print axioms Paper6TableOne.row_09_sigma_values
#print axioms Paper6TableOne.row_09_data
#print axioms Paper6TableOne.row_10
#print axioms Paper6TableOne.sigmaRow_10
#print axioms Paper6TableOne.row_10_structure
#print axioms Paper6TableOne.row_10_inclusion
#print axioms Paper6TableOne.row_10_length
#print axioms Paper6TableOne.row_10_sigma_select
#print axioms Paper6TableOne.row_10_sigma_01
#print axioms Paper6TableOne.row_10_sigma_02
#print axioms Paper6TableOne.row_10_sigma_03
#print axioms Paper6TableOne.row_10_sigma_04
#print axioms Paper6TableOne.row_10_signed
#print axioms Paper6TableOne.row_10_sigma_values
#print axioms Paper6TableOne.row_10_data
#print axioms Paper6TableOne.all_row_data
#print axioms Paper6TableOne.table_rows
#print axioms Paper6TableOne.monomial_degree_le
#print axioms Paper6TableOne.polyOf_degree_le
#print axioms Paper6TableOne.table_row_polynomial
#print axioms Paper6TableOne.evalFun_one_add_polyOf
#print axioms Paper6TableOne.complement_numbers
#print axioms Paper6TableOne.table_complements
#print axioms Paper6TableOne.table1_complete
#print axioms Paper6TableOne.check_Table1
#print Paper6TableOne.check_Table1
