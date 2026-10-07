import Research.Backfill.Paper5.Challenge
import Research.Backfill.Paper5.Supplement.AssociativityStatement
import Research.Backfill.Paper5.Supplement.FullPaperStatement
import Research.Backfill.Paper5.Supplement.AlgebraStatementV2

/-!
# Comparator challenge for Paper 5, version 2 (complete mappings of the Brauer and partial Brauer monoids)

For the comparator (https://github.com/leanprover/comparator). Every theorem below
states, with a `sorry` proof, exactly the type of the theorem of the same name in
`Research/Backfill/Paper5/Check.lean`, which is the solution module. This file is that
module with its imports replaced and each proof replaced by `sorry`; sections, namespaces
and `open` lines are unchanged. The statements refer only to the frozen statement file
`Research/Backfill/Paper5/Challenge.lean` (SHA-256 `ca2ff711…c373`), which imports only
Mathlib, and to the three supplementary statement files in
`Research/Backfill/Paper5/Supplement/`, which import only that file.

The `sorry`s are intentional: comparator checks that the solution proves the same
statements, using only the permitted axioms, and replays it in the Lean kernel and in
the independent kernel nanoda. This module is not imported by `Research.lean`.
-/

set_option autoImplicit false

-- Original literal Check group 1: ReesBasicCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.ReesBasicCheck
open BackfillPaper5.Challenge Function

theorem check_ZeroFixed :
  ∀ (S : Type) (op : S → S → S) (z : S), (∀ x, op z x = z ∧ op x z = z) →
    ∀ α : S → S, IsCompleteMapping op α → α z = z :=
  sorry


theorem check_Lemma41 :
  ∀ (r : ℕ) (H : Type) [Finite H] [Nonempty H] (P : H → H → Option (Sym r))
    (L : H → H → H) (phi : Sym r → Sym r),
    (∀ l, P l l = some 1) → IsLatin L → IsCompleteMapping (· * ·) phi →
      IsCompleteMapping (rees0Mul P) (fA L phi) :=
  sorry


end CodexPaper5.ReesBasicCheck

end

-- Original literal Check group 2: CycleRemarksCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.CycleRemarksCheck
open BackfillPaper5.Challenge Function

theorem check_Remark45a :
  ∀ (r : ℕ) (H : Type) [Finite H] (P : H → H → Option (Sym r)) (ρ : Equiv.Perm H),
    (∀ l, P l l = some 1) → (∀ l, CycleCond P ρ l) → ∀ l, ρ l ≠ l :=
  sorry


theorem check_Remark45b :
  ∀ (r : ℕ) (H : Type) [Finite H] (P : H → H → Option (Sym r)),
    (∀ l m p, P l m = some p → P m l = some p⁻¹) →
    ∀ (ρ : Equiv.Perm H) (l : H), ρ l ≠ l → ρ (ρ l) = l → P l (ρ l) ≠ none → CycleCond P ρ l :=
  sorry


theorem check_Remark45c :
  ∀ (r : ℕ) (H : Type) [Finite H] (P : H → H → Option (Sym r)) (ρ : Equiv.Perm H) (l : H)
    (pab pbc pca : Sym r),
    ρ l ≠ l → (ρ ^ 3) l = l →
    P l (ρ l) = some pab → P (ρ l) ((ρ ^ 2) l) = some pbc → P ((ρ ^ 2) l) l = some pca →
    (CycleCond P ρ l ↔ sgn pab + sgn pbc + sgn pca = 1) ∧
      (sgn pab + sgn pbc + sgn pca = 1 ↔ sgn (pab * pbc * pca) = 1) :=
  sorry


end CodexPaper5.CycleRemarksCheck

end

-- Original literal Check group 3: Lemma42Check.lean
section

set_option autoImplicit false

namespace CodexPaper5.Lemma42Check
open BackfillPaper5.Challenge Function

theorem check_Lemma42 :
  ∀ (r : ℕ), (r = 2 ∨ r = 3) → ∀ (H : Type) [Finite H] [Nonempty H]
    (P : H → H → Option (Sym r)), (∀ l, P l l = some 1) →
    (∃ f, IsCompleteMapping (mulZ2 (sgnMat P)) f) → ∃ f, IsCompleteMapping (rees0Mul P) f :=
  sorry


end CodexPaper5.Lemma42Check

end

-- Original literal Check group 4: ReesEvenCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.ReesEvenCheck

open BackfillPaper5.Challenge

/-- The full frozen statement, including both existential conclusions. -/
theorem check_Lemma43 :
  ∀ (r : ℕ), (r = 2 ∨ r = 3) → ∀ (H : Type) [Finite H] [Nonempty H]
    (P : H → H → Option (Sym r)), (∀ l, P l l = some 1) →
    (∀ (L : H → H → H) (δ : Equiv.Perm H) (t : H → ZMod 2), IsLatin L →
        (∀ μ, t (δ μ) = t μ + 1) → IsCompleteMapping (mulZ2 (sgnMat P)) (fB L δ t)) ∧
    (Even (Nat.card H) →
      (∃ (δ : Equiv.Perm H) (t : H → ZMod 2), ∀ μ, t (δ μ) = t μ + 1) ∧
        ∃ f, IsCompleteMapping (rees0Mul P) f) :=
  sorry


end CodexPaper5.ReesEvenCheck

end

-- Original literal Check group 5: ReesCycleCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.ReesCycleCheck

open BackfillPaper5.Challenge

/-- The full frozen statement, including the coefficient existence and the final Rees lift. -/
theorem check_Lemma44 :
  ∀ (r : ℕ), (r = 2 ∨ r = 3) → ∀ (H : Type) [Finite H] [Nonempty H]
    (P : H → H → Option (Sym r)), (∀ l, P l l = some 1) →
    ∀ ρ : Equiv.Perm H, (∀ l, P l (ρ l) ≠ none) → (∀ l, CycleCond P ρ l) →
      (∃ c : H → ZMod 2, ∀ l, c (ρ l) = c l + 1 + sOf P l (ρ l)) ∧
      (∀ (L : H → H → H) (c : H → ZMod 2), IsLatin L →
        (∀ l, c (ρ l) = c l + 1 + sOf P l (ρ l)) →
          IsCompleteMapping (mulZ2 (sgnMat P)) (fC L ρ c)) ∧
      ∃ f, IsCompleteMapping (rees0Mul P) f :=
  sorry


end CodexPaper5.ReesCycleCheck

end

-- Original literal Check group 6: SymmetricClassificationCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.SymmetricClassificationCheck

open BackfillPaper5.Challenge

theorem check_SymCM : ∀ r : ℕ, HasCM (Sym r) ↔ (r ≠ 2 ∧ r ≠ 3) :=
  sorry

theorem check_SymCMPerm : ∀ r : ℕ, HasCM (Equiv.Perm (Fin r)) ↔ (r ≠ 2 ∧ r ≠ 3) :=
  sorry


end CodexPaper5.SymmetricClassificationCheck

end

-- Original literal Check group 7: HalfDiagonalCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.HalfDiagonalCheck

open BackfillPaper5.Challenge

theorem check_Prop31d :
    ∀ (D : Fam) (n r : ℕ), ∀ l ∈ Hr D n r, ∀ i ∈ Hr D n r, l.1 = i.1 →
      Compat l i ∧ pSand r l i = 1 :=
  sorry


end CodexPaper5.HalfDiagonalCheck

end

-- Original literal Check group 8: DiagramCoordinatesCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.DiagramCoordinatesCheck

open BackfillPaper5.Challenge

theorem check_Prop31a :
  ∀ (D : Fam) (n r : ℕ), RankOccurs D n r →
    Set.BijOn (fun x => (topHalf x, gCoord r x, botHalf x)) (Jr D n r)
      (Hr D n r ×ˢ (Set.univ ×ˢ Hr D n r)) :=
  sorry


end CodexPaper5.DiagramCoordinatesCheck

end

-- Original literal Check group 9: GammaCompatibilityCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.GammaCompatibilityCheck

open BackfillPaper5.Challenge

theorem check_Prop31c :
    ∀ (D : Fam) (n r : ℕ), ∀ l ∈ Hr D n r, ∀ i ∈ Hr D n r,
      Compat l l ∧ pSand r l l = 1 ∧ (Compat l i ↔ Compat i l) ∧
        (Compat l i → pSand r i l = (pSand r l i)⁻¹) :=
  sorry


end CodexPaper5.GammaCompatibilityCheck

end

-- Original literal Check group 10: DiagramModelCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.DiagramModelCheck

open BackfillPaper5.Challenge

theorem check_ModelMonoid :
    ∀ n : ℕ, (∀ x ∈ PB n, ∀ y ∈ PB n, dmul x y ∈ PB n) ∧ (∀ x ∈ B n, ∀ y ∈ B n, dmul x y ∈ B n) ∧
      idD n ∈ B n ∧ ∀ x ∈ PB n, dmul (idD n) x = x ∧ dmul x (idD n) = x :=
  sorry


end CodexPaper5.DiagramModelCheck

end

-- Original literal Check group 11: DiagramRankCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.DiagramRankCheck

open BackfillPaper5.Challenge

theorem check_RankMul :
    ∀ n : ℕ, ∀ x ∈ PB n, ∀ y ∈ PB n, rank (dmul x y) ≤ min (rank x) (rank y) :=
  sorry


end CodexPaper5.DiagramRankCheck

end

-- Original literal Check group 12: DiagramProductCoordinatesCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.DiagramProductCoordinatesCheck

open BackfillPaper5.Challenge

theorem check_Prop31b :
    ∀ (D : Fam) (n r : ℕ), ∀ x ∈ Jr D n r, ∀ y ∈ Jr D n r,
      (rank (dmul x y) = r ↔ Compat (botHalf x) (topHalf y)) ∧
      (Compat (botHalf x) (topHalf y) →
        topHalf (dmul x y) = topHalf x ∧ botHalf (dmul x y) = botHalf y ∧
        gCoord r (dmul x y) = gCoord r x * pSand r (botHalf x) (topHalf y) * gCoord r y) :=
  sorry


end CodexPaper5.DiagramProductCoordinatesCheck

end

-- Original literal Check group 13: DiagramPrincipalFactorCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.DiagramPrincipalFactorCheck

open BackfillPaper5.Challenge

open Classical in
theorem check_Prop31iso :
  ∀ (D : Fam) (n r : ℕ), RankOccurs D n r →
    ∃ e : Option (Jr D n r) ≃ Option (HSub D n r × Sym r × HSub D n r),
      e none = none ∧
      (∀ (x : Jr D n r) (t : HSub D n r × Sym r × HSub D n r), e (some x) = some t →
        t.1.1 = topHalf x.1 ∧ t.2.1 = gCoord r x.1 ∧ t.2.2.1 = botHalf x.1) ∧
      ∀ u v, e (pfMul dmul (Jr D n r) u v) = rees0Mul (sandSub D n r) (e u) (e v) :=
  sorry


end CodexPaper5.DiagramPrincipalFactorCheck

end

-- Original literal Check group 14: DiagramIdempotentCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.DiagramIdempotentCheck

open BackfillPaper5.Challenge

theorem check_IdempotentE :
  ∀ (D : Fam) (n r : ℕ), ∀ l ∈ Hr D n r,
    eDiag l ∈ Jr D n r ∧ topHalf (eDiag l) = l ∧ botHalf (eDiag l) = l ∧
    gCoord r (eDiag l) = 1 ∧ dmul (eDiag l) (eDiag l) = eDiag l ∧
    ∀ x ∈ Jr D n r, ∀ y ∈ Jr D n r, topHalf x = l → botHalf x = l → topHalf y = l →
      botHalf y = l →
      dmul x y ∈ Jr D n r ∧ topHalf (dmul x y) = l ∧ botHalf (dmul x y) = l ∧
        gCoord r (dmul x y) = gCoord r x * gCoord r y :=
  sorry


end CodexPaper5.DiagramIdempotentCheck

end

-- Original literal Check group 15: DiagramJClassesCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.DiagramJClassesCheck

open BackfillPaper5.Challenge

theorem check_JClassesAreRankClasses :
  ∀ (D : Fam) (n : ℕ), ∀ x ∈ Dset D n, ∀ y ∈ Dset D n,
    (JRel dmul (Dset D n) x y ↔ rank x = rank y) :=
  sorry


end CodexPaper5.DiagramJClassesCheck

end

-- Original literal Check group 16: DiagramUnitGroupCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.DiagramUnitGroupCheck

open BackfillPaper5.Challenge

theorem check_UnitsAreSym :
  ∀ (D : Fam) (n : ℕ),
    (∀ x ∈ Dset D n,
      (∃ y ∈ Dset D n, dmul x y = idD n ∧ dmul y x = idD n) ↔ rank x = n) ∧
    ∃ e : Sym n ≃ Jr D n n, ∀ g h : Sym n, ((e (g * h) : Jr D n n) : Pt n → Pt n) = dmul (e g) (e h) :=
  sorry


end CodexPaper5.DiagramUnitGroupCheck

end

-- Original literal Check group 17: DiagramRanksOccurringCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.DiagramRanksOccurringCheck

open BackfillPaper5.Challenge

theorem check_RanksOccurring :
  ∀ n r : ℕ, (RankOccurs Fam.B n r ↔ r ≤ n ∧ r % 2 = n % 2) ∧ (RankOccurs Fam.PB n r ↔ r ≤ n) :=
  sorry


end CodexPaper5.DiagramRanksOccurringCheck

end

-- Original literal Check group 18: HalfFibreCountingCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.HalfFibreCountingCheck

open BackfillPaper5.Challenge
open scoped Nat

theorem check_FibreCount :
  ∀ n r : ℕ, r ≤ n → r % 2 = n % 2 → ∀ F : Finset (Fin n), F.card = r →
    {h | h ∈ Hr Fam.B n r ∧ h.1 = F}.ncard = (n - r - 1)‼ ∧ Odd ((n - r - 1)‼) :=
  sorry


end CodexPaper5.HalfFibreCountingCheck

end

-- Original literal Check group 19: HalfCountingCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.HalfCountingCheck

open BackfillPaper5.Challenge
open scoped Nat

theorem check_CountH :
  (∀ n r : ℕ, r ≤ n → r % 2 = n % 2 → (Hr Fam.B n r).ncard = n.choose r * (n - r - 1)‼) ∧
    (∀ n r : ℕ, r ≤ n → (Hr Fam.PB n r).ncard = n.choose r * invCount (n - r)) :=
  sorry


end CodexPaper5.HalfCountingCheck

end

-- Original literal Check group 20: BrauerParityCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.BrauerParityCheck

open BackfillPaper5.Challenge

theorem check_Lemma51 :
  ∀ n r : ℕ, (r = 2 ∨ r = 3) → r < n → n % 2 = r % 2 →
    (Odd (Hr Fam.B n r).ncard ↔ (r = 2 ∧ n % 4 = 2) ∨ (r = 3 ∧ n % 4 = 3)) ∧
    (Odd (Hr Fam.B n r).ncard → 4 ≤ n - r ∧ Odd (n.choose r)) :=
  sorry


end CodexPaper5.BrauerParityCheck

end

-- Original literal Check group 21: PartialBrauerParityCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.PartialBrauerParityCheck

open BackfillPaper5.Challenge

theorem check_Lemma61 :
  (∀ k : ℕ, 2 ≤ k → Even (invCount k)) ∧
    ∀ n r : ℕ, 4 ≤ n → (r = 2 ∨ r = 3) → r < n →
      Even (n.choose r * invCount (n - r)) ∧ Even (Hr Fam.PB n r).ncard :=
  sorry


end CodexPaper5.PartialBrauerParityCheck

end

-- Original literal Check group 22: Prop62Check.lean
section

set_option autoImplicit false

namespace CodexPaper5.Prop62Check

open BackfillPaper5.Challenge

open Classical in
theorem check_Prop62 :
  MagmaIso (pfMul dmul (Jr Fam.PB 3 2)) (rees0Mul delta3) ∧ ¬ PFHasCM dmul (Jr Fam.PB 3 2) :=
  sorry


end CodexPaper5.Prop62Check

end

-- Original literal Check group 23: BrauerTriangleCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.BrauerTriangleCheck

open BackfillPaper5.Challenge

open Classical in
theorem check_Lemma52 :
  ∀ n r : ℕ, (r = 2 ∨ r = 3) → r + 2 ≤ n → n % 2 = r % 2 →
    (∀ j, triHalf n r j ∈ Hr Fam.B n r) ∧
    Compat (triHalf n r 0) (triHalf n r 1) ∧ Compat (triHalf n r 1) (triHalf n r 2) ∧
    Compat (triHalf n r 2) (triHalf n r 0) ∧
    pSand r (triHalf n r 0) (triHalf n r 1) = 1 ∧ pSand r (triHalf n r 1) (triHalf n r 2) = 1 ∧
    pSand r (triHalf n r 2) (triHalf n r 0) = swap12 r ∧
    sgn (pSand r (triHalf n r 0) (triHalf n r 1) * pSand r (triHalf n r 1) (triHalf n r 2) *
      pSand r (triHalf n r 2) (triHalf n r 0)) = 1 :=
  sorry


end CodexPaper5.BrauerTriangleCheck

end

-- Original literal Check group 24: BrauerTriangleProductCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.BrauerTriangleProductCheck

open BackfillPaper5.Challenge

open Classical in
theorem check_TriangleProduct :
  ∀ n r : ℕ, (r = 2 ∨ r = 3) → r + 2 ≤ n → n % 2 = r % 2 →
    let e : Fin 3 → Pt n → Pt n := fun j => eDiag (triHalf n r j)
    let x := dmul (dmul (dmul (e 0) (e 1)) (e 2)) (e 0)
    x ∈ Jr Fam.B n r ∧ topHalf x = triHalf n r 0 ∧ botHalf x = triHalf n r 0 ∧
      gCoord r x = pSand r (triHalf n r 0) (triHalf n r 1) * pSand r (triHalf n r 1) (triHalf n r 2) *
        pSand r (triHalf n r 2) (triHalf n r 0) ∧
      sgn (gCoord r x) = 1 :=
  sorry


end CodexPaper5.BrauerTriangleProductCheck

end

-- Original literal Check group 25: BrauerJoinCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.BrauerJoinCheck

open BackfillPaper5.Challenge

open Classical in
theorem check_Lemma53 :
  ∀ n r : ℕ, r ≤ n → n % 2 = r % 2 →
    ∀ F F' : Finset (Fin n), F.card = r → F'.card = r →
    F ≠ F' → r + 2 * (F \ F').card ≤ n →
      ∃ v ∈ Hr Fam.B n r, ∃ w ∈ Hr Fam.B n r,
        v.1 = F ∧ w.1 = F' ∧ Compat v w :=
  sorry


end CodexPaper5.BrauerJoinCheck

end

-- Original literal Check group 26: BrauerMatchingCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.BrauerMatchingCheck

open BackfillPaper5.Challenge

open Classical in
theorem check_Lemma54 :
  ∀ n r : ℕ, (r = 2 ∨ r = 3) → r < n → n % 2 = r % 2 → 4 ≤ n - r → Odd (n.choose r) →
    ∃ δ : Half n → Half n,
      ∀ v ∈ Hr Fam.B n r \ {triHalf n r 0, triHalf n r 1, triHalf n r 2},
        δ v ∈ Hr Fam.B n r \ {triHalf n r 0, triHalf n r 1, triHalf n r 2} ∧
          δ (δ v) = v ∧ δ v ≠ v ∧ Compat v (δ v) :=
  sorry


end CodexPaper5.BrauerMatchingCheck

end

-- Original literal Check group 27: MainABCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.MainABCheck

open BackfillPaper5.Challenge

open Classical in
theorem check_Thm11a :
    ∀ n : ℕ, 1 ≤ n → ∀ x ∈ B n, ¬ JRel dmul (B n) x (idD n) →
      PFHasCM dmul (JClass dmul (B n) x) :=
  sorry

open Classical in
theorem check_Thm11b :
    ∀ n : ℕ, 1 ≤ n → ∀ x ∈ PB n, ¬ JRel dmul (PB n) x (idD n) →
      (PFHasCM dmul (JClass dmul (PB n) x) ↔ ¬ (n = 3 ∧ rank x = 2)) ∧
      (n = 3 → rank x = 2 →
        MagmaIso (pfMul dmul (JClass dmul (PB n) x)) (rees0Mul delta3)) :=
  sorry


end CodexPaper5.MainABCheck

end

-- Original literal Check group 28: MainCCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.MainCCheck

open BackfillPaper5.Challenge

theorem check_Thm11c :
  ∀ n : ℕ, 1 ≤ n →
    (SubsetHasCM dmul (B n) ↔ SubsetHasCM dmul (PB n)) ∧
    (SubsetHasCM dmul (PB n) ↔ HasCM (Sym n)) ∧
    (HasCM (Sym n) ↔ (n = 1 ∨ 4 ≤ n)) :=
  sorry


end CodexPaper5.MainCCheck

end

-- Original literal Check group 29: AssocMainCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.AssocMainCheck

open BackfillPaper5

theorem check_PBAssociativity :
    ∀ (n : ℕ) (x y z : Challenge.Pt n → Challenge.Pt n),
      Challenge.IsPB x → Challenge.IsPB y → Challenge.IsPB z →
      Challenge.dmul (Challenge.dmul x y) z =
        Challenge.dmul x (Challenge.dmul y z) :=
  sorry

theorem check_BAssociativity :
    ∀ (n : ℕ) (x y z : Challenge.Pt n → Challenge.Pt n),
      x ∈ Challenge.B n → y ∈ Challenge.B n → z ∈ Challenge.B n →
      Challenge.dmul (Challenge.dmul x y) z =
        Challenge.dmul x (Challenge.dmul y z) :=
  sorry

theorem check_PBMonoidAligned :
    ∀ n : ℕ, ∃ M : Monoid ↥(Challenge.Dset Challenge.Fam.PB n),
      (∀ x y : ↥(Challenge.Dset Challenge.Fam.PB n),
        (@Mul.mul ↥(Challenge.Dset Challenge.Fam.PB n) M.toMul x y).val =
          Challenge.dmul x.val y.val) ∧
      (@One.one ↥(Challenge.Dset Challenge.Fam.PB n) M.toOne).val = Challenge.idD n :=
  sorry

theorem check_BMonoidAligned :
    ∀ n : ℕ, ∃ M : Monoid ↥(Challenge.Dset Challenge.Fam.B n),
      (∀ x y : ↥(Challenge.Dset Challenge.Fam.B n),
        (@Mul.mul ↥(Challenge.Dset Challenge.Fam.B n) M.toMul x y).val =
          Challenge.dmul x.val y.val) ∧
      (@One.one ↥(Challenge.Dset Challenge.Fam.B n) M.toOne).val = Challenge.idD n :=
  sorry

end CodexPaper5.AssocMainCheck


end

-- Original literal Check group 30: AssocGraphCompressionCheck.lean
section

set_option autoImplicit false

universe u v

namespace CodexPaper5.AssocGraphCompressionCheck

theorem check_ReachableElimination :
  ∀ (V : Type u) (W : Type v) (f : W ↪ V) (G : SimpleGraph V)
    (C H : SimpleGraph W),
    (∀ p q : W, G.Reachable (f p) (f q) ↔ C.Reachable p q) →
    ∀ p q : W,
      (G ⊔ H.map f).Reachable (f p) (f q) ↔ (C ⊔ H).Reachable p q :=
  sorry

end CodexPaper5.AssocGraphCompressionCheck


end

-- Original literal Check group 31: AssocGeometryCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.AssocGeometryCheck

open BackfillPaper5

theorem check_OuterBracketReachability :
  ∀ (n : ℕ) (x y z : Challenge.Pt n → Challenge.Pt n),
    Challenge.IsPB x → Challenge.IsPB y → Challenge.IsPB z →
    ∀ p q : Challenge.Pt n,
      (Challenge.stackGraph (Challenge.dmul x y) z).Reachable
        (Challenge.outer p) (Challenge.outer q) ↔
      (Challenge.stackGraph x (Challenge.dmul y z)).Reachable
        (Challenge.outer p) (Challenge.outer q) :=
  sorry

end CodexPaper5.AssocGeometryCheck


end

-- Original literal Check group 32: FullPaperAllNCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.FullPaperAllNCheck

open BackfillPaper5

theorem check_AllNClassification :
    ∀ n : ℕ,
      (Challenge.SubsetHasCM Challenge.dmul (Challenge.B n) ↔
        Challenge.SubsetHasCM Challenge.dmul (Challenge.PB n)) ∧
      (Challenge.SubsetHasCM Challenge.dmul (Challenge.PB n) ↔
        Challenge.HasCM (Challenge.Sym n)) ∧
      (Challenge.HasCM (Challenge.Sym n) ↔ n ≠ 2 ∧ n ≠ 3) :=
  sorry

end CodexPaper5.FullPaperAllNCheck


end

-- Original literal Check group 33: FullPaperCornerCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.FullPaperCornerCheck

open BackfillPaper5
open CodexPaper5.FullPaperStatement

theorem check_CornerGroupAligned :
    ∀ (D : Challenge.Fam) (n r : ℕ) (l : Challenge.Half n),
      l ∈ Challenge.Hr D n r →
      ∃ M : Group (Corner D n r l),
        letI : Group (Corner D n r l) := M
        ∃ e : Corner D n r l ≃* Challenge.Sym r,
          (∀ x y : Corner D n r l,
            (x * y).val = Challenge.dmul x.val y.val) ∧
          (1 : Corner D n r l).val = Challenge.eDiag l ∧
          (∀ x : Corner D n r l, e x = Challenge.gCoord r x.val) :=
  sorry

end CodexPaper5.FullPaperCornerCheck


end

-- Original literal Check group 34: GenericAlgebraCheck.lean
section

set_option autoImplicit false

universe u v w

namespace CodexPaper5.GenericAlgebraCheck

open BackfillPaper5

theorem check_ReesAssociativity :
    ∀ (G : Type u) (I : Type v) (L : Type w)
      (M : Semigroup G) (P : L → I → Option G),
      letI : Semigroup G := M
      ∀ x y z : Challenge.Rees0 G I L,
        Challenge.rees0Mul P (Challenge.rees0Mul P x y) z =
          Challenge.rees0Mul P x (Challenge.rees0Mul P y z) :=
  sorry

theorem check_CayleyTransversalIff :
    ∀ (S : Type u) (op : S → S → S),
      (∃ a : S → S, Challenge.IsCompleteMapping op a) ↔
        ∃ T : Set (S × S),
          Function.Bijective (fun x : T => x.val.1) ∧
          Function.Bijective (fun x : T => x.val.2) ∧
          Function.Bijective (fun x : T => op x.val.1 x.val.2) :=
  sorry

end CodexPaper5.GenericAlgebraCheck


end

-- Original literal Check group 35: NumericHalfCountsCheck.lean
section

set_option autoImplicit false

namespace CodexPaper5.NumericHalfCountsCheck

open BackfillPaper5

theorem check_HalfCount45 : (Challenge.Hr Challenge.Fam.B 6 2).ncard = 45 :=
  sorry

theorem check_HalfCount105 : (Challenge.Hr Challenge.Fam.B 7 3).ncard = 105 :=
  sorry

end CodexPaper5.NumericHalfCountsCheck


end
