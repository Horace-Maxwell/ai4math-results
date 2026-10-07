import Research.Backfill.Paper5.Challenge

/-!
# Known-answer tests for the paper-5 challenge definitions (addendum 1, item 2)

Kernel-checked (`decide +kernel`), plus a few short proofs for `Function.minimalPeriod`, which
is not computable. This file is not part of the frozen challenge; it only tests its definitions.
Paper points are 1-based; `Fin` indices are 0-based.

Diagrams used below (`n = 2`):
* `idD 2`: blocks `{1,1'}, {2,2'}` (identity);
* `cross`: blocks `{1,2'}, {2,1'}` (the transposition);
* `cup`: blocks `{1,2}, {1',2'}` (rank 0; `cup · cup = cup`, the closed loop is discarded).
`single 1`: the diagram of `PB_1` with two singletons `{1}, {1'}`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 4000000

namespace BackfillPaper5.ChallengeTests

open BackfillPaper5.Challenge

/-! ### Test-only instances (`Function.Involutive` is a `def`; Mathlib has no `Fintype αᵐᵒᵖ`) -/

instance instFintypeSym (r : ℕ) : Fintype (Sym r) := Fintype.ofEquiv _ MulOpposite.opEquiv

instance instDecPB (n : ℕ) : DecidablePred (· ∈ PB n) := fun x =>
  inferInstanceAs (Decidable (∀ p, x (x p) = p))

instance instDecB (n : ℕ) : DecidablePred (· ∈ B n) := fun x =>
  inferInstanceAs (Decidable ((∀ p, x (x p) = p) ∧ ∀ p, x p ≠ p))

instance instDecJr (D : Fam) (n r : ℕ) : DecidablePred (· ∈ Jr D n r) := fun x =>
  match D with
  | .B => inferInstanceAs (Decidable (((∀ p, x (x p) = p) ∧ ∀ p, x p ≠ p) ∧ rank x = r))
  | .PB => inferInstanceAs (Decidable ((∀ p, x (x p) = p) ∧ rank x = r))

instance instDecHalf (D : Fam) (n r : ℕ) : DecidablePred (IsHalf D n r) := fun h =>
  inferInstanceAs (Decidable (h.1.card = r ∧ (∀ a, h.2 (h.2 a) = a) ∧ (∀ a ∈ h.1, h.2 a = a) ∧
    (D = Fam.B → ∀ a, a ∉ h.1 → h.2 a ≠ a)))

/-! ### Example diagrams -/

/-- `{1,2'}, {2,1'}`. -/
def cross : Pt 2 → Pt 2
  | .inl i => .inr i.rev
  | .inr i => .inl i.rev

/-- `{1,2}, {1',2'}`. -/
def cup : Pt 2 → Pt 2
  | .inl i => .inl i.rev
  | .inr i => .inr i.rev

/-- `{1}, {1'}` (two singletons). -/
def single1 : Pt 1 → Pt 1 := id

/-! ### 1. `IsCompleteMapping`, `HasCM` (source: Hall–Paige; [ABCHK, Thm 1.1]) -/

-- `S_1` (trivial) has a complete mapping; `S_2` has none (paper §2, from (R1)).
theorem test_001 : HasCM (Sym 1) := by unfold HasCM IsCompleteMapping; decide +kernel
theorem test_002 : ¬ HasCM (Sym 2) := by unfold HasCM IsCompleteMapping; decide +kernel
-- odd-order cyclic group: yes; cyclic group of order 2: no
theorem test_003 : HasCM (Multiplicative (ZMod 3)) := by unfold HasCM IsCompleteMapping; decide +kernel
theorem test_004 : ¬ HasCM (Multiplicative (ZMod 2)) := by unfold HasCM IsCompleteMapping; decide +kernel

/-! ### 2. `MagmaIso` -/

theorem test_005 : MagmaIso (fun a b : Bool => a && b) (fun a b => a || b) := by
  unfold MagmaIso; decide +kernel
theorem test_006 : ¬ MagmaIso (fun a b : Bool => a && b) (fun a b => xor a b) := by
  unfold MagmaIso; decide +kernel

/-! ### 3. `Sym`, `sgn`, `swap12` -/

theorem test_007 : sgn (swap12 2) = 1 ∧ sgn (swap12 3) = 1 ∧ sgn (1 : Sym 3) = 0 := by decide +kernel
-- `Sym r` multiplies left to right: `(1 2)` then `(2 3)` sends `1 ↦ 2 ↦ 3` (0-based: 0 ↦ 2)
theorem test_008 : (MulOpposite.unop (MulOpposite.op (Equiv.swap (0 : Fin 3) 1) *
    MulOpposite.op (Equiv.swap (1 : Fin 3) 2))) 0 = 2 := by decide +kernel
-- the sign is additive: odd * odd = even
theorem test_009 : sgn (swap12 3 * swap12 3) = 0 := by decide +kernel

/-! ### 4. `rees0Mul`, `delta3` (the Brandt semigroup `B(S₂,3)`) -/

theorem test_010 : rees0Mul delta3 (some (0, swap12 2, 1)) (some (1, swap12 2, 2)) = some (0, 1, 2) := by
  decide +kernel
theorem test_011 : rees0Mul delta3 (some (0, swap12 2, 1)) (some (2, 1, 2)) = none := by decide +kernel
theorem test_012 : rees0Mul delta3 none (some (2, 1, 2)) = none := by decide +kernel
theorem test_013 : rees0Mul delta3 (some (0, 1, 1)) (some (1, 1, 2)) ≠ some (0, swap12 2, 2) := by
  decide +kernel

/-! ### 5. `mulZ2`, `sgnMat`, `sOf` -/

/-- A sandwich matrix over `S₂` on `H = ZMod 2`: identity diagonal, `(1 2)` off the diagonal. -/
def Pex : ZMod 2 → ZMod 2 → Option (Sym 2) := fun l j => if l = j then some 1 else some (swap12 2)

theorem test_014 : sOf Pex 0 0 = 0 ∧ sOf Pex 0 1 = 1 ∧ sgnMat Pex 1 0 = some 1 := by decide +kernel
theorem test_015 : mulZ2 (sgnMat Pex) (some (0, 1, 0)) (some (1, 1, 1)) = some (0, 1, 1) := by
  decide +kernel
theorem test_016 : mulZ2 (sgnMat delta3) (some (0, 1, 0)) (some (1, 1, 1)) = none := by decide +kernel

/-! ### 6. `IsLatin` -/

theorem test_017 : IsLatin (fun i l : ZMod 3 => i + l) := by unfold IsLatin; decide +kernel
theorem test_018 : ¬ IsLatin (fun i _ : ZMod 3 => i) := by unfold IsLatin; decide +kernel

/-! ### 7. `fA`, `fB`, `fC` (small instances of Lemmas 4.1, 4.3, 4.4; mutations must fail) -/

-- Lemma 4.1 with `r = 1`, `H = ZMod 2`, `L = +`, `φ = id` (`S_1` trivial)
theorem test_019 : IsCompleteMapping (rees0Mul (fun l j : ZMod 2 => if l = j then some (1 : Sym 1) else none))
    (fA (fun i l : ZMod 2 => i + l) id) := by unfold IsCompleteMapping; decide +kernel
-- Lemma 4.3 (i) with `H = ZMod 2`, `δ μ = μ + 1`, `t = id`: a complete mapping
theorem test_020 : IsCompleteMapping
    (mulZ2 (sgnMat (fun l j : ZMod 2 => if l = j then some (1 : Sym 2) else none)))
    (fB (fun i l : ZMod 2 => i + l) (fun μ => μ + 1) id) := by
  unfold IsCompleteMapping; decide +kernel
-- mutation: `t = 0` violates `t (δ μ) = t μ + 1`; then `fB` is not a complete mapping
theorem test_021 : ¬ IsCompleteMapping
    (mulZ2 (sgnMat (fun l j : ZMod 2 => if l = j then some (1 : Sym 2) else none)))
    (fB (fun i l : ZMod 2 => i + l) (fun μ => μ + 1) (fun _ => 0)) := by
  unfold IsCompleteMapping; decide +kernel
-- Lemma 4.4 (ii) with `ρ = swap`, all entries `1` (so `s = 0`), `c = id`
theorem test_022 : IsCompleteMapping (mulZ2 (sgnMat (fun _ _ : ZMod 2 => some (1 : Sym 2))))
    (fC (fun i l : ZMod 2 => i + l) (fun l => l + 1) id) := by
  unfold IsCompleteMapping; decide +kernel
-- mutation: `ρ = id` (a fixed point, violating `(∗)`): not a complete mapping
theorem test_023 : ¬ IsCompleteMapping (mulZ2 (sgnMat (fun _ _ : ZMod 2 => some (1 : Sym 2))))
    (fC (fun i l : ZMod 2 => i + l) id id) := by
  unfold IsCompleteMapping; decide +kernel

/-! ### 8. `CycleCond` (uses `Function.minimalPeriod`, not computable: short proofs) -/

-- a transposition with even entries satisfies `(∗)` (`m = 2`); a fixed point does not (`m = 1`)
theorem test_024 : CycleCond (fun _ _ : ZMod 2 => some (1 : Sym 2)) (Equiv.swap 0 1) 0 := by
  have hper : Function.IsPeriodicPt (Equiv.swap (0 : ZMod 2) 1) 2 0 := by
    show (Equiv.swap (0 : ZMod 2) 1)^[2] 0 = 0
    decide +kernel
  have hfix : ¬ Function.IsFixedPt (Equiv.swap (0 : ZMod 2) 1) 0 := by
    show ¬ (Equiv.swap (0 : ZMod 2) 1) 0 = 0
    decide +kernel
  have h2 : Function.minimalPeriod (Equiv.swap (0 : ZMod 2) 1) 0 = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Function.minimalPeriod_eq_prime hper hfix
  unfold CycleCond
  rw [h2]
  decide +kernel
theorem test_025 : ¬ CycleCond (fun _ _ : ZMod 2 => some (1 : Sym 2)) (1 : Equiv.Perm (ZMod 2)) 0 := by
  have h1 : Function.minimalPeriod (⇑(1 : Equiv.Perm (ZMod 2))) 0 = 1 := by
    rw [Equiv.Perm.coe_one]; exact Function.minimalPeriod_id
  unfold CycleCond
  rw [h1]
  decide +kernel

/-! ### 9. Diagrams: `IsPB`, `PB`, `B`, `idD`, sizes (paper Table 2: `|B_1| = 1`, `|PB_1| = 2`) -/

theorem test_026 : idD 2 ∈ B 2 ∧ cross ∈ B 2 ∧ cup ∈ B 2 ∧ single1 ∈ PB 1 := by decide +kernel
theorem test_027 : single1 ∉ B 1 := by decide +kernel
theorem test_028 : Fintype.card {x : Pt 1 → Pt 1 // x ∈ B 1} = 1 := by decide +kernel
theorem test_029 : Fintype.card {x : Pt 1 → Pt 1 // x ∈ PB 1} = 2 := by decide +kernel
-- `|B_2| = 3!! = 3`, `|PB_2| = a(4) = 10`
theorem test_030 : Fintype.card {x : Pt 2 → Pt 2 // x ∈ B 2} = 3 := by decide +kernel
theorem test_031 : Fintype.card {x : Pt 2 → Pt 2 // x ∈ PB 2} = 10 := by decide +kernel

/-! ### 10. `rank`, `topHalf`, `botHalf`, `pos` -/

theorem test_032 : rank (idD 2) = 2 ∧ rank cross = 2 ∧ rank cup = 0 ∧ rank single1 = 0 := by decide +kernel
theorem test_033 : rank cup ≠ 1 := by decide +kernel
theorem test_034 : (topHalf cup).1 = ∅ ∧ (topHalf cup).2 0 = 1 ∧ (botHalf cup).2 1 = 0 ∧
    (topHalf (idD 2)).1 = Finset.univ ∧ (botHalf cross).1 = Finset.univ := by decide +kernel
theorem test_035 : pos ({1, 3, 4} : Finset (Fin 6)) 3 = 1 ∧ pos ({1, 3, 4} : Finset (Fin 6)) 1 = 0 ∧
    pos ({1, 3, 4} : Finset (Fin 6)) 5 = 3 := by decide +kernel

/-! ### 11. The product `dmul` (paper §2: loops and middle components are discarded) -/

theorem test_036 : dmul (idD 2) cup = cup := by funext p; revert p; decide +kernel
theorem test_037 : dmul cup (idD 2) = cup := by funext p; revert p; decide +kernel
-- closed loop discarded
theorem test_038 : dmul cup cup = cup := by funext p; revert p; decide +kernel
theorem test_039 : dmul cross cross = idD 2 := by funext p; revert p; decide +kernel
theorem test_040 : dmul cup cup ≠ idD 2 := by
  intro h; have := congrFun h (Sum.inl 0); revert this; decide +kernel
-- partial Brauer: singletons; a middle component is discarded
theorem test_041 : dmul single1 single1 = single1 := by funext p; revert p; decide +kernel
theorem test_042 : dmul (idD 1) single1 = single1 := by funext p; revert p; decide +kernel

/-! ### 12. `Jr`, `RankOccurs`, `JRel`, `JClass` -/

theorem test_043 : idD 2 ∈ Jr Fam.B 2 2 ∧ cup ∈ Jr Fam.B 2 0 ∧ cup ∉ Jr Fam.B 2 2 := by decide +kernel
-- `J_1(B_2)` is empty (`r ≢ n mod 2`), `J_1(PB_2)` is not (paper §2)
theorem test_044 : ¬ RankOccurs Fam.B 2 1 := by
  unfold RankOccurs Dset; decide +kernel
theorem test_045 : RankOccurs Fam.PB 2 1 := by
  unfold RankOccurs Dset; decide +kernel
-- `J`-classes in `PB_1`: `{single1}` and `{idD 1}`
theorem test_046 : JRel dmul (PB 1) single1 single1 := by unfold JRel; decide +kernel
theorem test_047 : ¬ JRel dmul (PB 1) single1 (idD 1) := by unfold JRel; decide +kernel

/-! ### 13. `pfMul`, `PFHasCM`, `SubsetHasCM` -/

-- the group-of-units factor of `B_2` is `S_2` with a zero: no complete mapping (paper §7)
theorem test_048 : ¬ PFHasCM dmul (Jr Fam.B 2 2) := by
  unfold PFHasCM IsCompleteMapping; decide +kernel
-- the rank-0 factor of `PB_1` has one
theorem test_049 : PFHasCM dmul (Jr Fam.PB 1 0) := by
  unfold PFHasCM IsCompleteMapping; decide +kernel
-- `B_1` has a complete mapping (paper Table 2: certificate for `B_1`); `B_2` has none (Thm 1.1(c))
theorem test_050 : SubsetHasCM dmul (B 1) := by unfold SubsetHasCM; decide +kernel
theorem test_051 : ¬ SubsetHasCM dmul (B 2) := by unfold SubsetHasCM; decide +kernel

/-! ### 14. `IsHalf`, `Hr` (paper, proof of Prop 6.2: `H_2(PB_3)` = three pairs `(F, ∅)`) -/

theorem test_052 : Fintype.card {h : Half 3 // IsHalf Fam.PB 3 2 h} = 3 := by decide +kernel
-- `N = C(4,2) · 1!! = 6` for `B_4`, rank 2; `N = 3!! = 3` for rank 0
theorem test_053 : Fintype.card {h : Half 4 // IsHalf Fam.B 4 2 h} = 6 := by decide +kernel
theorem test_054 : Fintype.card {h : Half 4 // IsHalf Fam.B 4 0 h} = 3 := by decide +kernel
theorem test_055 : ¬ IsHalf Fam.B 4 2 ({2, 3}, id) ∧ IsHalf Fam.PB 4 2 ({2, 3}, id) := by decide +kernel

/-! ### 15. `triHalf`, `r0`, `eDiag` (Lemma 5.2) -/

theorem test_056 : (triHalf 4 2 0).1 = {2, 3} ∧ (triHalf 4 2 1).1 = {1, 3} ∧ (triHalf 4 2 2).1 = {1, 2} := by
  decide +kernel
theorem test_057 : (triHalf 5 3 0).1 = {2, 3, 4} ∧ (triHalf 5 3 2).1 = {1, 2, 4} := by decide +kernel
theorem test_058 : (triHalf 6 2 0).2 0 = 1 ∧ (triHalf 6 2 1).2 0 = 2 ∧ (triHalf 6 2 2).2 0 = 3 ∧
    (triHalf 6 2 0).2 4 = 5 ∧ (triHalf 6 2 0).2 5 = 4 := by decide +kernel
theorem test_059 : (triHalf 7 3 1).2 5 = 6 ∧ (triHalf 7 3 1).2 4 = 4 ∧ (triHalf 10 2 0).2 9 = 8 := by
  decide +kernel
theorem test_060 : IsHalf Fam.B 6 2 (triHalf 6 2 0) ∧ IsHalf Fam.B 7 3 (triHalf 7 3 2) := by decide +kernel
theorem test_061 : rank (eDiag (triHalf 4 2 0)) = 2 ∧ topHalf (eDiag (triHalf 4 2 0)) = triHalf 4 2 0 ∧
    eDiag (triHalf 4 2 0) ∈ B 4 := by decide +kernel

/-! ### 16. `Compat`, `RepP`, `RepG` (Lemma 5.2 for `(n,r) = (4,2)`; Prop 6.2) -/

theorem test_062 : Compat (triHalf 4 2 0) (triHalf 4 2 1) ∧ Compat (triHalf 4 2 1) (triHalf 4 2 2) ∧
    Compat (triHalf 4 2 2) (triHalf 4 2 0) := by unfold Compat; decide +kernel
-- in `PB_3`, different free sets are incompatible (proof of Prop 6.2)
theorem test_063 : ¬ Compat (({0, 1} : Finset (Fin 3)), id) (({0, 2} : Finset (Fin 3)), id) := by
  unfold Compat; decide +kernel
-- `p_{I₂I₀} = (1 2)` and `p_{I₀I₁} = 1`, and not the other way round
theorem test_064 : RepP 2 (triHalf 4 2 2) (triHalf 4 2 0) (swap12 2) ∧ RepP 2 (triHalf 4 2 0) (triHalf 4 2 1) 1 := by
  unfold RepP; decide +kernel
theorem test_065 : ¬ RepP 2 (triHalf 4 2 2) (triHalf 4 2 0) 1 := by unfold RepP; decide +kernel
-- `g(idD) = 1`, `g(cross) = (1 2)`
theorem test_066 : RepG 2 (idD 2) 1 ∧ RepG 2 cross (swap12 2) ∧ ¬ RepG 2 cross 1 := by
  unfold RepG; decide +kernel

/-! ### 17. `invCount` (paper, proof of Lemma 6.1: `a(2) = 2`, `a(3) = 4`) -/

theorem test_067 : invCount 0 = 1 ∧ invCount 1 = 1 ∧ invCount 2 = 2 ∧ invCount 3 = 4 := by
  simp only [invCount, Nat.card_eq_fintype_card]; decide +kernel
theorem test_068 : invCount 4 = 10 := by simp only [invCount, Nat.card_eq_fintype_card]; decide +kernel

end BackfillPaper5.ChallengeTests

/-! Named declarations for the retained tests; audit each helper and test by its full name. -/

#print axioms BackfillPaper5.ChallengeTests.instFintypeSym
#print axioms BackfillPaper5.ChallengeTests.instDecPB
#print axioms BackfillPaper5.ChallengeTests.instDecB
#print axioms BackfillPaper5.ChallengeTests.instDecJr
#print axioms BackfillPaper5.ChallengeTests.instDecHalf
#print axioms BackfillPaper5.ChallengeTests.cross
#print axioms BackfillPaper5.ChallengeTests.cup
#print axioms BackfillPaper5.ChallengeTests.single1
#print axioms BackfillPaper5.ChallengeTests.Pex
#print axioms BackfillPaper5.ChallengeTests.test_001
#print axioms BackfillPaper5.ChallengeTests.test_002
#print axioms BackfillPaper5.ChallengeTests.test_003
#print axioms BackfillPaper5.ChallengeTests.test_004
#print axioms BackfillPaper5.ChallengeTests.test_005
#print axioms BackfillPaper5.ChallengeTests.test_006
#print axioms BackfillPaper5.ChallengeTests.test_007
#print axioms BackfillPaper5.ChallengeTests.test_008
#print axioms BackfillPaper5.ChallengeTests.test_009
#print axioms BackfillPaper5.ChallengeTests.test_010
#print axioms BackfillPaper5.ChallengeTests.test_011
#print axioms BackfillPaper5.ChallengeTests.test_012
#print axioms BackfillPaper5.ChallengeTests.test_013
#print axioms BackfillPaper5.ChallengeTests.test_014
#print axioms BackfillPaper5.ChallengeTests.test_015
#print axioms BackfillPaper5.ChallengeTests.test_016
#print axioms BackfillPaper5.ChallengeTests.test_017
#print axioms BackfillPaper5.ChallengeTests.test_018
#print axioms BackfillPaper5.ChallengeTests.test_019
#print axioms BackfillPaper5.ChallengeTests.test_020
#print axioms BackfillPaper5.ChallengeTests.test_021
#print axioms BackfillPaper5.ChallengeTests.test_022
#print axioms BackfillPaper5.ChallengeTests.test_023
#print axioms BackfillPaper5.ChallengeTests.test_024
#print axioms BackfillPaper5.ChallengeTests.test_025
#print axioms BackfillPaper5.ChallengeTests.test_026
#print axioms BackfillPaper5.ChallengeTests.test_027
#print axioms BackfillPaper5.ChallengeTests.test_028
#print axioms BackfillPaper5.ChallengeTests.test_029
#print axioms BackfillPaper5.ChallengeTests.test_030
#print axioms BackfillPaper5.ChallengeTests.test_031
#print axioms BackfillPaper5.ChallengeTests.test_032
#print axioms BackfillPaper5.ChallengeTests.test_033
#print axioms BackfillPaper5.ChallengeTests.test_034
#print axioms BackfillPaper5.ChallengeTests.test_035
#print axioms BackfillPaper5.ChallengeTests.test_036
#print axioms BackfillPaper5.ChallengeTests.test_037
#print axioms BackfillPaper5.ChallengeTests.test_038
#print axioms BackfillPaper5.ChallengeTests.test_039
#print axioms BackfillPaper5.ChallengeTests.test_040
#print axioms BackfillPaper5.ChallengeTests.test_041
#print axioms BackfillPaper5.ChallengeTests.test_042
#print axioms BackfillPaper5.ChallengeTests.test_043
#print axioms BackfillPaper5.ChallengeTests.test_044
#print axioms BackfillPaper5.ChallengeTests.test_045
#print axioms BackfillPaper5.ChallengeTests.test_046
#print axioms BackfillPaper5.ChallengeTests.test_047
#print axioms BackfillPaper5.ChallengeTests.test_048
#print axioms BackfillPaper5.ChallengeTests.test_049
#print axioms BackfillPaper5.ChallengeTests.test_050
#print axioms BackfillPaper5.ChallengeTests.test_051
#print axioms BackfillPaper5.ChallengeTests.test_052
#print axioms BackfillPaper5.ChallengeTests.test_053
#print axioms BackfillPaper5.ChallengeTests.test_054
#print axioms BackfillPaper5.ChallengeTests.test_055
#print axioms BackfillPaper5.ChallengeTests.test_056
#print axioms BackfillPaper5.ChallengeTests.test_057
#print axioms BackfillPaper5.ChallengeTests.test_058
#print axioms BackfillPaper5.ChallengeTests.test_059
#print axioms BackfillPaper5.ChallengeTests.test_060
#print axioms BackfillPaper5.ChallengeTests.test_061
#print axioms BackfillPaper5.ChallengeTests.test_062
#print axioms BackfillPaper5.ChallengeTests.test_063
#print axioms BackfillPaper5.ChallengeTests.test_064
#print axioms BackfillPaper5.ChallengeTests.test_065
#print axioms BackfillPaper5.ChallengeTests.test_066
#print axioms BackfillPaper5.ChallengeTests.test_067
#print axioms BackfillPaper5.ChallengeTests.test_068
