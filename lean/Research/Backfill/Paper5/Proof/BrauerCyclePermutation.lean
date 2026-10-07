import Research.Backfill.Paper5.Proof.BrauerMatching
import Research.Backfill.Paper5.Proof.BrauerTriangleProduct

set_option autoImplicit false

namespace CodexPaper5.BrauerCyclePermutation

open BackfillPaper5
open BrauerMatchingFibres

/-- The frozen triangle vertices, as actual legal Brauer half-diagrams. -/
def triSub {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (j : Fin 3) : Challenge.HSub Challenge.Fam.B n r :=
  ⟨Challenge.triHalf n r j, BrauerTriangleBasics.triHalf_mem_hr n r hr hn hpar j⟩

def remSub {n r : ℕ} (a : Target n r) : Challenge.HSub Challenge.Fam.B n r :=
  ⟨a.val, ((target_mem_iff n r a.val).mp a.property).1⟩

theorem triHalf_injective {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n) :
    Function.Injective (Challenge.triHalf n r) := by
  intro i j h
  exact BrauerMatchingLabels.triHalf_free_injective n r hr hn (congrArg Prod.fst h)

theorem triSub_injective {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) : Function.Injective (triSub hr hn hpar) := by
  intro i j h
  exact triHalf_injective hr hn (congrArg Subtype.val h)

open Classical in
noncomputable def splitForward {n r : ℕ} (l : Challenge.HSub Challenge.Fam.B n r) :
    Fin 3 ⊕ Target n r :=
  if hs : ∃ j : Fin 3, l.val = Challenge.triHalf n r j then
    Sum.inl hs.choose
  else
    Sum.inr ⟨l.val, (target_mem_iff n r l.val).mpr
      ⟨l.property, fun j hj => hs ⟨j, hj⟩⟩⟩

def splitBackward {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) : Fin 3 ⊕ Target n r → Challenge.HSub Challenge.Fam.B n r
  | Sum.inl j => triSub hr hn hpar j
  | Sum.inr a => remSub a

theorem splitForward_tri {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (j : Fin 3) :
    splitForward (triSub hr hn hpar j) = Sum.inl j := by
  classical
  have hs : ∃ k : Fin 3, (triSub hr hn hpar j).val = Challenge.triHalf n r k := ⟨j, rfl⟩
  rw [splitForward, dite_eq_left hs]
  exact congrArg Sum.inl (triHalf_injective hr hn hs.choose_spec).symm

theorem splitForward_rem {n r : ℕ} (a : Target n r) :
    splitForward (remSub a) = Sum.inr a := by
  classical
  have hs : ¬ ∃ j : Fin 3, (remSub a).val = Challenge.triHalf n r j := by
    rintro ⟨j, hj⟩
    exact ((target_mem_iff n r a.val).mp a.property).2 j hj
  unfold splitForward
  exact dite_eq_right hs

theorem split_left_inv {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (l : Challenge.HSub Challenge.Fam.B n r) :
    splitBackward hr hn hpar (splitForward l) = l := by
  classical
  by_cases hs : ∃ j : Fin 3, l.val = Challenge.triHalf n r j
  · rw [splitForward, dite_eq_left hs]
    exact Subtype.ext hs.choose_spec.symm
  · rw [splitForward, dite_eq_right hs]
    rfl

theorem split_right_inv {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (z : Fin 3 ⊕ Target n r) :
    splitForward (splitBackward hr hn hpar z) = z := by
  cases z with
  | inl j => exact splitForward_tri hr hn hpar j
  | inr a => exact splitForward_rem a

/-- This split removes exactly three Half values, rather than three whole fibres. -/
noncomputable def splitEquiv {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) : Challenge.HSub Challenge.Fam.B n r ≃ Fin 3 ⊕ Target n r where
  toFun := splitForward
  invFun := splitBackward hr hn hpar
  left_inv := split_left_inv hr hn hpar
  right_inv := split_right_inv hr hn hpar

def prevIndex : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 0
  | 2 => 1

def triangleCycle : Equiv.Perm (Fin 3) where
  toFun := BrauerTriangle.nextIndex
  invFun := prevIndex
  left_inv j := by fin_cases j <;> rfl
  right_inv j := by fin_cases j <;> rfl

theorem nextIndex_ne (j : Fin 3) : BrauerTriangle.nextIndex j ≠ j := by
  fin_cases j <;> decide

theorem nextIndex_cube (j : Fin 3) :
    BrauerTriangle.nextIndex (BrauerTriangle.nextIndex (BrauerTriangle.nextIndex j)) = j := by
  fin_cases j <;> rfl

def pairPermutation {n r : ℕ} (δ : Target n r → Target n r)
    (hδI : Function.Involutive δ) : Equiv.Perm (Target n r) where
  toFun := δ
  invFun := δ
  left_inv := hδI
  right_inv := hδI

/-- The genuine three-cycle and the genuine remainder involution are conjugated by the split. -/
noncomputable def cyclePermutation {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (δ : Target n r → Target n r)
    (hδI : Function.Involutive δ) : Equiv.Perm (Challenge.HSub Challenge.Fam.B n r) :=
  (splitEquiv hr hn hpar).trans
    ((Equiv.sumCongr triangleCycle (pairPermutation δ hδI)).trans (splitEquiv hr hn hpar).symm)

theorem cyclePermutation_tri {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (δ : Target n r → Target n r)
    (hδI : Function.Involutive δ) (j : Fin 3) :
    cyclePermutation hr hn hpar δ hδI (triSub hr hn hpar j) =
      triSub hr hn hpar (BrauerTriangle.nextIndex j) := by
  change (splitEquiv hr hn hpar).symm
    (Sum.map triangleCycle (pairPermutation δ hδI) (splitForward (triSub hr hn hpar j))) = _
  rw [splitForward_tri hr hn hpar j]
  rfl

theorem cyclePermutation_rem {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (δ : Target n r → Target n r)
    (hδI : Function.Involutive δ) (a : Target n r) :
    cyclePermutation hr hn hpar δ hδI (remSub a) = remSub (δ a) := by
  change (splitEquiv hr hn hpar).symm
    (Sum.map triangleCycle (pairPermutation δ hδI) (splitForward (remSub a))) = _
  rw [splitForward_rem a]
  rfl

theorem cyclePermutation_ne {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (δ : Target n r → Target n r)
    (hδI : Function.Involutive δ) (hδN : ∀ a, δ a ≠ a)
    (l : Challenge.HSub Challenge.Fam.B n r) : cyclePermutation hr hn hpar δ hδI l ≠ l := by
  obtain ⟨z, rfl⟩ := (splitEquiv hr hn hpar).symm.surjective l
  cases z with
  | inl j =>
      change cyclePermutation hr hn hpar δ hδI (triSub hr hn hpar j) ≠ triSub hr hn hpar j
      rw [cyclePermutation_tri]
      intro h
      exact nextIndex_ne j (triSub_injective hr hn hpar h)
  | inr a =>
      change cyclePermutation hr hn hpar δ hδI (remSub a) ≠ remSub a
      rw [cyclePermutation_rem]
      intro h
      have hv : (δ a).val = a.val :=
        congrArg (fun z : Challenge.HSub Challenge.Fam.B n r => z.val) h
      exact hδN a (Subtype.ext hv)

theorem triangle_compat {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n) (j : Fin 3) :
    Challenge.Compat (Challenge.triHalf n r j)
      (Challenge.triHalf n r (BrauerTriangle.nextIndex j)) := by
  fin_cases j
  · exact BrauerTriangle.compat_01 n r hr hn
  · exact BrauerTriangle.compat_12 n r hr hn
  · exact BrauerTriangle.compat_20 n r hr hn

theorem cyclePermutation_compat {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (δ : Target n r → Target n r)
    (hδI : Function.Involutive δ) (hδC : ∀ a, Challenge.Compat a.val (δ a).val)
    (l : Challenge.HSub Challenge.Fam.B n r) :
    Challenge.Compat l.val (cyclePermutation hr hn hpar δ hδI l).val := by
  obtain ⟨z, rfl⟩ := (splitEquiv hr hn hpar).symm.surjective l
  cases z with
  | inl j =>
      change Challenge.Compat (triSub hr hn hpar j).val
        (cyclePermutation hr hn hpar δ hδI (triSub hr hn hpar j)).val
      rw [cyclePermutation_tri]
      exact triangle_compat hr hn j
  | inr a =>
      change Challenge.Compat (remSub a).val
        (cyclePermutation hr hn hpar δ hδI (remSub a)).val
      rw [cyclePermutation_rem]
      exact hδC a

theorem sandSub_some {D : Challenge.Fam} {n r : ℕ} (l m : Challenge.HSub D n r)
    (hc : Challenge.Compat l.val m.val) :
    Challenge.sandSub D n r l m = some (Challenge.pSand r l.val m.val) := by
  simp only [Challenge.sandSub, Challenge.sand, ite_eq_left hc]

theorem sandSub_ne_none {D : Challenge.Fam} {n r : ℕ} (l m : Challenge.HSub D n r)
    (hc : Challenge.Compat l.val m.val) : Challenge.sandSub D n r l m ≠ none := by
  rw [sandSub_some l m hc]
  exact Option.some_ne_none _

/-- Reversal is established only on actual nonzero entries of legal half-diagrams. -/
theorem sandSub_reverse {D : Challenge.Fam} {n r : ℕ} (l m : Challenge.HSub D n r)
    (p : Challenge.Sym r) (hp : Challenge.sandSub D n r l m = some p) :
    Challenge.sandSub D n r m l = some p⁻¹ := by
  classical
  by_cases hc : Challenge.Compat l.val m.val
  · have he : Challenge.pSand r l.val m.val = p :=
      Option.some.inj ((sandSub_some l m hc).symm.trans hp)
    rw [sandSub_some m l (GammaCompatibility.compat_symm l.property m.property hc),
      GammaCompatibility.pSand_reverse l.property m.property hc, he]
  · simp only [Challenge.sandSub, Challenge.sand, ite_eq_right hc] at hp
    cases hp

/-- The sign is extracted from the actual fixed left-bracket diagram product. -/
theorem triangle_edge_sign_sum {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (j : Fin 3) :
    Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r j)
        (Challenge.triHalf n r (BrauerTriangle.nextIndex j))) +
      Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r (BrauerTriangle.nextIndex j))
        (Challenge.triHalf n r (BrauerTriangle.nextIndex (BrauerTriangle.nextIndex j)))) +
      Challenge.sgn (Challenge.pSand r
        (Challenge.triHalf n r (BrauerTriangle.nextIndex (BrauerTriangle.nextIndex j)))
        (Challenge.triHalf n r j)) = 1 := by
  have hx := BrauerTriangleProduct.check_TriangleProduct n r hr hn hpar
  have hs := hx.2.2.2.2
  rw [hx.2.2.2.1, CycleRemarks.sgn_mul, CycleRemarks.sgn_mul] at hs
  fin_cases j
  · exact hs
  · calc
      _ = Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 0) (Challenge.triHalf n r 1)) +
          Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 1) (Challenge.triHalf n r 2)) +
          Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 2) (Challenge.triHalf n r 0)) := by
            change
              Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 1) (Challenge.triHalf n r 2)) +
                Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 2) (Challenge.triHalf n r 0)) +
                Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 0) (Challenge.triHalf n r 1)) =
              Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 0) (Challenge.triHalf n r 1)) +
                Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 1) (Challenge.triHalf n r 2)) +
                Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 2) (Challenge.triHalf n r 0))
            abel
      _ = 1 := hs
  · calc
      _ = Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 0) (Challenge.triHalf n r 1)) +
          Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 1) (Challenge.triHalf n r 2)) +
          Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 2) (Challenge.triHalf n r 0)) := by
            change
              Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 2) (Challenge.triHalf n r 0)) +
                Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 0) (Challenge.triHalf n r 1)) +
                Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 1) (Challenge.triHalf n r 2)) =
              Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 0) (Challenge.triHalf n r 1)) +
                Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 1) (Challenge.triHalf n r 2)) +
                Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 2) (Challenge.triHalf n r 0))
            abel
      _ = 1 := hs

/-- Each of the three actual origins satisfies the frozen condition; no group-product rotation
is asserted. Only the abelian sign sums are rotated. -/
theorem triangle_cycle_cond {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (ρ : Equiv.Perm (Challenge.HSub Challenge.Fam.B n r))
    (htri : ∀ j, ρ (triSub hr hn hpar j) = triSub hr hn hpar (BrauerTriangle.nextIndex j))
    (j : Fin 3) : Challenge.CycleCond (Challenge.sandSub Challenge.Fam.B n r) ρ
      (triSub hr hn hpar j) := by
  have hne : ρ (triSub hr hn hpar j) ≠ triSub hr hn hpar j := by
    rw [htri]
    intro h
    exact nextIndex_ne j (triSub_injective hr hn hpar h)
  have htwo : (ρ ^ 2) (triSub hr hn hpar j) =
      triSub hr hn hpar (BrauerTriangle.nextIndex (BrauerTriangle.nextIndex j)) := by
    rw [pow_two, Equiv.Perm.mul_apply, htri, htri]
  have hthree : (ρ ^ 3) (triSub hr hn hpar j) = triSub hr hn hpar j := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ', Equiv.Perm.mul_apply,
      pow_two, Equiv.Perm.mul_apply, htri, htri, htri, nextIndex_cube]
  have hab : Challenge.sandSub Challenge.Fam.B n r (triSub hr hn hpar j)
      (ρ (triSub hr hn hpar j)) = some (Challenge.pSand r
        (Challenge.triHalf n r j) (Challenge.triHalf n r (BrauerTriangle.nextIndex j))) := by
    rw [htri]
    exact sandSub_some _ _ (triangle_compat hr hn j)
  have hbc : Challenge.sandSub Challenge.Fam.B n r (ρ (triSub hr hn hpar j))
      ((ρ ^ 2) (triSub hr hn hpar j)) = some (Challenge.pSand r
        (Challenge.triHalf n r (BrauerTriangle.nextIndex j))
        (Challenge.triHalf n r (BrauerTriangle.nextIndex (BrauerTriangle.nextIndex j)))) := by
    rw [htri, htwo]
    exact sandSub_some _ _ (triangle_compat hr hn (BrauerTriangle.nextIndex j))
  have hca : Challenge.sandSub Challenge.Fam.B n r ((ρ ^ 2) (triSub hr hn hpar j))
      (triSub hr hn hpar j) = some (Challenge.pSand r
        (Challenge.triHalf n r (BrauerTriangle.nextIndex (BrauerTriangle.nextIndex j)))
        (Challenge.triHalf n r j)) := by
    rw [htwo]
    have hc := triangle_compat hr hn (BrauerTriangle.nextIndex (BrauerTriangle.nextIndex j))
    rw [nextIndex_cube] at hc
    exact sandSub_some _ _ hc
  exact (CodexPaper5.check_Remark45c r (Challenge.HSub Challenge.Fam.B n r)
    (Challenge.sandSub Challenge.Fam.B n r) ρ (triSub hr hn hpar j) _ _ _
    hne hthree hab hbc hca).1.mpr (triangle_edge_sign_sum hr hn hpar j)

theorem cyclePermutation_cycleCond {n r : ℕ} (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (δ : Target n r → Target n r)
    (hδI : Function.Involutive δ) (hδN : ∀ a, δ a ≠ a)
    (hδC : ∀ a, Challenge.Compat a.val (δ a).val)
    (l : Challenge.HSub Challenge.Fam.B n r) :
    Challenge.CycleCond (Challenge.sandSub Challenge.Fam.B n r)
      (cyclePermutation hr hn hpar δ hδI) l := by
  obtain ⟨z, rfl⟩ := (splitEquiv hr hn hpar).symm.surjective l
  cases z with
  | inl j =>
      exact triangle_cycle_cond hr hn hpar (cyclePermutation hr hn hpar δ hδI)
        (cyclePermutation_tri hr hn hpar δ hδI) j
  | inr a =>
      change Challenge.CycleCond (Challenge.sandSub Challenge.Fam.B n r)
        (cyclePermutation hr hn hpar δ hδI) (remSub a)
      have hret : cyclePermutation hr hn hpar δ hδI
          (cyclePermutation hr hn hpar δ hδI (remSub a)) = remSub a := by
        rw [cyclePermutation_rem, cyclePermutation_rem, hδI a]
      exact CodexPaper5.check_Remark45b r (Challenge.HSub Challenge.Fam.B n r)
        (Challenge.sandSub Challenge.Fam.B n r) sandSub_reverse
        (cyclePermutation hr hn hpar δ hδI) (remSub a)
        (cyclePermutation_ne hr hn hpar δ hδI hδN (remSub a)) hret
        (sandSub_ne_none _ _ (cyclePermutation_compat hr hn hpar δ hδI hδC (remSub a)))

/-- All hypotheses are discharged on the actual HSub: the accepted matching supplies the
remainder involution, and the accepted diagram product supplies the triangle parity. -/
theorem exists_cycle_permutation {n r : ℕ} (hr : r = 2 ∨ r = 3) (hrn : r < n)
    (hpar : n % 2 = r % 2) (hgap : 4 ≤ n - r) (hchoose : Odd (n.choose r)) :
    ∃ ρ : Equiv.Perm (Challenge.HSub Challenge.Fam.B n r),
      (∀ l, Challenge.sandSub Challenge.Fam.B n r l (ρ l) ≠ none) ∧
        (∀ l, Challenge.CycleCond (Challenge.sandSub Challenge.Fam.B n r) ρ l) := by
  have hn : r + 2 ≤ n := by omega
  obtain ⟨δ, hδI, hδN, hδC⟩ :=
    BrauerMatching.exists_target_pairing n r hr hrn hpar hgap hchoose
  refine ⟨cyclePermutation hr hn hpar δ hδI, ?_, ?_⟩
  · intro l
    exact sandSub_ne_none _ _ (cyclePermutation_compat hr hn hpar δ hδI hδC l)
  · exact cyclePermutation_cycleCond hr hn hpar δ hδI hδN hδC

end CodexPaper5.BrauerCyclePermutation

#print axioms CodexPaper5.BrauerCyclePermutation.triSub
#print axioms CodexPaper5.BrauerCyclePermutation.remSub
#print axioms CodexPaper5.BrauerCyclePermutation.triHalf_injective
#print axioms CodexPaper5.BrauerCyclePermutation.triSub_injective
#print axioms CodexPaper5.BrauerCyclePermutation.splitForward
#print axioms CodexPaper5.BrauerCyclePermutation.splitBackward
#print axioms CodexPaper5.BrauerCyclePermutation.splitForward_tri
#print axioms CodexPaper5.BrauerCyclePermutation.splitForward_rem
#print axioms CodexPaper5.BrauerCyclePermutation.split_left_inv
#print axioms CodexPaper5.BrauerCyclePermutation.split_right_inv
#print axioms CodexPaper5.BrauerCyclePermutation.splitEquiv
#print axioms CodexPaper5.BrauerCyclePermutation.prevIndex
#print axioms CodexPaper5.BrauerCyclePermutation.triangleCycle
#print axioms CodexPaper5.BrauerCyclePermutation.nextIndex_ne
#print axioms CodexPaper5.BrauerCyclePermutation.nextIndex_cube
#print axioms CodexPaper5.BrauerCyclePermutation.pairPermutation
#print axioms CodexPaper5.BrauerCyclePermutation.cyclePermutation
#print axioms CodexPaper5.BrauerCyclePermutation.cyclePermutation_tri
#print axioms CodexPaper5.BrauerCyclePermutation.cyclePermutation_rem
#print axioms CodexPaper5.BrauerCyclePermutation.cyclePermutation_ne
#print axioms CodexPaper5.BrauerCyclePermutation.triangle_compat
#print axioms CodexPaper5.BrauerCyclePermutation.cyclePermutation_compat
#print axioms CodexPaper5.BrauerCyclePermutation.sandSub_some
#print axioms CodexPaper5.BrauerCyclePermutation.sandSub_ne_none
#print axioms CodexPaper5.BrauerCyclePermutation.sandSub_reverse
#print axioms CodexPaper5.BrauerCyclePermutation.triangle_edge_sign_sum
#print axioms CodexPaper5.BrauerCyclePermutation.triangle_cycle_cond
#print axioms CodexPaper5.BrauerCyclePermutation.cyclePermutation_cycleCond
#print axioms CodexPaper5.BrauerCyclePermutation.exists_cycle_permutation
