import Research.Backfill.Paper5.Proof.BrauerTriangleBasics
import Research.Backfill.Paper5.Proof.GammaCompatibility
import Research.Backfill.Paper5.Proof.SignSmall

set_option autoImplicit false

namespace CodexPaper5.BrauerTriangle

open BackfillPaper5

/-- The three triangle vertices in their frozen cyclic order. -/
def nextIndex : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- The increasing free-point label at a rank coordinate. -/
def freeLabel : Fin 3 → ℕ → ℕ
  | 0, k => k + 2
  | 1, k => if k = 0 then 1 else k + 2
  | 2, k => if k < 2 then k + 1 else k + 2

theorem freeLabel_lt (r : ℕ) (hr : r = 2 ∨ r = 3) (j : Fin 3) (k : Fin r) :
    freeLabel j k.val < r + 2 := by
  rcases hr with rfl | rfl <;> fin_cases j <;> fin_cases k <;> norm_num [freeLabel]

/-- The actual point of Fin n with the indicated increasing free-point label. -/
def freePoint (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (j : Fin 3) (k : Fin r) : Fin n :=
  ⟨freeLabel j k.val, lt_of_lt_of_le (freeLabel_lt r hr j k) hn⟩

theorem freePoint_mem (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (j : Fin 3) (k : Fin r) :
    freePoint n r hr hn j k ∈ (Challenge.triHalf n r j).1 := by
  apply (BrauerTriangleBasics.triHalf_free_iff n r j _).mpr
  change freeLabel j k.val < r + 2 ∧ freeLabel j k.val ≠ 0 ∧
    freeLabel j k.val ≠ Challenge.triPartner j
  rcases hr with rfl | rfl <;> fin_cases j <;> fin_cases k <;>
    norm_num [freeLabel, Challenge.triPartner]

/-- Compute the frozen counting position on the six exact actual free sets. -/
theorem pos_freePoint (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (j : Fin 3) (k : Fin r) :
    Challenge.pos (Challenge.triHalf n r j).1 (freePoint n r hr hn j k) = k.val := by
  rcases hr with rfl | rfl
  · fin_cases j <;> fin_cases k <;>
      simp [Challenge.pos, freePoint, freeLabel, Fin.lt_def,
        BrauerTriangleBasics.triHalf_free_two_0 n hn,
        BrauerTriangleBasics.triHalf_free_two_1 n hn,
        BrauerTriangleBasics.triHalf_free_two_2 n hn]
    all_goals norm_num [Finset.filter_insert, Finset.filter_singleton, Fin.ext_iff]
  · fin_cases j <;> fin_cases k <;>
      simp [Challenge.pos, freePoint, freeLabel, Fin.lt_def,
        BrauerTriangleBasics.triHalf_free_three_0 n hn,
        BrauerTriangleBasics.triHalf_free_three_1 n hn,
        BrauerTriangleBasics.triHalf_free_three_2 n hn]
    all_goals norm_num [Finset.filter_insert, Finset.filter_singleton, Fin.ext_iff]

theorem triPartner_pos (j : Fin 3) : 0 < Challenge.triPartner j := by
  fin_cases j <;> norm_num [Challenge.triPartner]

/-- Each exceptional free point follows the other half's arc to zero, then the first arc out. -/
theorem reachable_via_zero (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (j t : Fin 3) (a b : Fin n) (ha : a.val = Challenge.triPartner t)
    (hb : b.val = Challenge.triPartner j) :
    (Challenge.gammaGraph (Challenge.triHalf n r j) (Challenge.triHalf n r t)).Reachable a b := by
  have hr2 : 2 ≤ r := by rcases hr with rfl | rfl <;> omega
  let z : Fin n := ⟨0, by omega⟩
  have haz : a ≠ z := by
    intro heq
    have hv : a.val = 0 := congrArg Fin.val heq
    rw [ha] at hv
    exact (Nat.ne_of_gt (triPartner_pos t)) hv
  have hbz : b ≠ z := by
    intro heq
    have hv : b.val = 0 := congrArg Fin.val heq
    rw [hb] at hv
    exact (Nat.ne_of_gt (triPartner_pos j)) hv
  have htz : (Challenge.triHalf n r t).2 a = z := by
    apply Fin.ext
    exact BrauerTriangleBasics.triHalf_match_partner_val n r hr hn t a ha
  have hjb : (Challenge.triHalf n r j).2 z = b := by
    apply Fin.ext
    exact (BrauerTriangleBasics.triHalf_match_zero_val n r hr hn j z rfl).trans hb.symm
  have hadj : (Challenge.gammaGraph (Challenge.triHalf n r j)
      (Challenge.triHalf n r t)).Adj a z := by
    change a ≠ z ∧
      (Challenge.GammaEdge (Challenge.triHalf n r j) (Challenge.triHalf n r t) a z ∨
        Challenge.GammaEdge (Challenge.triHalf n r j) (Challenge.triHalf n r t) z a)
    exact ⟨haz, Or.inl (Or.inr ⟨htz, Ne.symm haz⟩)⟩
  have hbadj : (Challenge.gammaGraph (Challenge.triHalf n r j)
      (Challenge.triHalf n r t)).Adj z b := by
    change z ≠ b ∧
      (Challenge.GammaEdge (Challenge.triHalf n r j) (Challenge.triHalf n r t) z b ∨
        Challenge.GammaEdge (Challenge.triHalf n r j) (Challenge.triHalf n r t) b z)
    exact ⟨Ne.symm hbz, Or.inl (Or.inl ⟨hjb, hbz⟩)⟩
  exact hadj.reachable.trans hbadj.reachable

theorem compat_01 (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n) :
    Challenge.Compat (Challenge.triHalf n r 0) (Challenge.triHalf n r 1) := by
  have hr2 : 2 ≤ r := by rcases hr with rfl | rfl <;> omega
  intro a ha
  have haf := (BrauerTriangleBasics.triHalf_free_iff n r 0 a).mp ha
  by_cases ha2 : a.val = 2
  · let b : Fin n := ⟨1, by omega⟩
    refine ⟨b, ?_, reachable_via_zero n r hr hn 0 1 a b ?_ ?_⟩
    · apply (BrauerTriangleBasics.triHalf_free_iff n r 1 b).mpr
      change 1 < r + 2 ∧ 1 ≠ 0 ∧ 1 ≠ 2
      omega
    · simpa only [Challenge.triPartner] using ha2
    · rfl
  · refine ⟨a, ?_, SimpleGraph.Reachable.rfl⟩
    apply (BrauerTriangleBasics.triHalf_free_iff n r 1 a).mpr
    exact ⟨haf.1, haf.2.1, by simpa only [Challenge.triPartner] using ha2⟩

theorem compat_12 (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n) :
    Challenge.Compat (Challenge.triHalf n r 1) (Challenge.triHalf n r 2) := by
  have hr2 : 2 ≤ r := by rcases hr with rfl | rfl <;> omega
  intro a ha
  have haf := (BrauerTriangleBasics.triHalf_free_iff n r 1 a).mp ha
  by_cases ha3 : a.val = 3
  · let b : Fin n := ⟨2, by omega⟩
    refine ⟨b, ?_, reachable_via_zero n r hr hn 1 2 a b ?_ ?_⟩
    · apply (BrauerTriangleBasics.triHalf_free_iff n r 2 b).mpr
      change 2 < r + 2 ∧ 2 ≠ 0 ∧ 2 ≠ 3
      omega
    · simpa only [Challenge.triPartner] using ha3
    · rfl
  · refine ⟨a, ?_, SimpleGraph.Reachable.rfl⟩
    apply (BrauerTriangleBasics.triHalf_free_iff n r 2 a).mpr
    exact ⟨haf.1, haf.2.1, by simpa only [Challenge.triPartner] using ha3⟩

theorem compat_20 (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n) :
    Challenge.Compat (Challenge.triHalf n r 2) (Challenge.triHalf n r 0) := by
  have hr2 : 2 ≤ r := by rcases hr with rfl | rfl <;> omega
  intro a ha
  have haf := (BrauerTriangleBasics.triHalf_free_iff n r 2 a).mp ha
  by_cases ha1 : a.val = 1
  · let b : Fin n := ⟨3, by omega⟩
    refine ⟨b, ?_, reachable_via_zero n r hr hn 2 0 a b ?_ ?_⟩
    · apply (BrauerTriangleBasics.triHalf_free_iff n r 0 b).mpr
      change 3 < r + 2 ∧ 3 ≠ 0 ∧ 3 ≠ 1
      omega
    · simpa only [Challenge.triPartner] using ha1
    · rfl
  · refine ⟨a, ?_, SimpleGraph.Reachable.rfl⟩
    apply (BrauerTriangleBasics.triHalf_free_iff n r 0 a).mpr
    exact ⟨haf.1, haf.2.1, by simpa only [Challenge.triPartner] using ha1⟩

theorem compat_next (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n) (j : Fin 3) :
    Challenge.Compat (Challenge.triHalf n r j) (Challenge.triHalf n r (nextIndex j)) := by
  fin_cases j
  · exact compat_01 n r hr hn
  · exact compat_12 n r hr hn
  · exact compat_20 n r hr hn

/-- The actual opposite permutation expected on each oriented triangle edge. -/
def expectedSand (r : ℕ) (j : Fin 3) : Challenge.Sym r :=
  if j = 2 then Challenge.swap12 r else 1

/-- The explicit paths realize every rank coordinate, including coordinate two when r=3. -/
theorem freePoint_reachable (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (j : Fin 3) (k : Fin r) :
    (Challenge.gammaGraph (Challenge.triHalf n r j)
      (Challenge.triHalf n r (nextIndex j))).Reachable
      (freePoint n r hr hn j k)
      (freePoint n r hr hn (nextIndex j) ((MulOpposite.unop (expectedSand r j)) k)) := by
  rcases hr with rfl | rfl <;> fin_cases j <;> fin_cases k
  all_goals
    simp [freePoint, freeLabel, nextIndex, expectedSand, Challenge.swap12, Equiv.swap_apply_def]
  all_goals
    apply reachable_via_zero n _ (by simp) hn <;> norm_num [Challenge.triPartner]

/-- Evaluate the full already verified RepP specification along those concrete paths. -/
theorem pSand_next (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (j : Fin 3) :
    Challenge.pSand r (Challenge.triHalf n r j) (Challenge.triHalf n r (nextIndex j)) =
      expectedSand r j := by
  have hl := BrauerTriangleBasics.triHalf_mem_hr n r hr hn hpar j
  have hi := BrauerTriangleBasics.triHalf_mem_hr n r hr hn hpar (nextIndex j)
  have hc := compat_next n r hr hn j
  have hp := GammaCompatibility.repP_pSand hl hi hc
  apply MulOpposite.unop_injective
  apply Equiv.ext
  intro k
  apply Fin.ext
  have hval := hp k (freePoint n r hr hn j k)
    (freePoint n r hr hn (nextIndex j) ((MulOpposite.unop (expectedSand r j)) k))
    (freePoint_mem n r hr hn j k)
    (freePoint_mem n r hr hn (nextIndex j) ((MulOpposite.unop (expectedSand r j)) k))
    (pos_freePoint n r hr hn j k) (freePoint_reachable n r hr hn j k)
  rw [pos_freePoint] at hval
  exact hval

theorem pSand_01 (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) :
    Challenge.pSand r (Challenge.triHalf n r 0) (Challenge.triHalf n r 1) = 1 := by
  simpa [nextIndex, expectedSand] using pSand_next n r hr hn hpar 0

theorem pSand_12 (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) :
    Challenge.pSand r (Challenge.triHalf n r 1) (Challenge.triHalf n r 2) = 1 := by
  simpa [nextIndex, expectedSand] using pSand_next n r hr hn hpar 1

theorem pSand_20 (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) :
    Challenge.pSand r (Challenge.triHalf n r 2) (Challenge.triHalf n r 0) = Challenge.swap12 r := by
  simpa [nextIndex, expectedSand] using pSand_next n r hr hn hpar 2

theorem triangle_sign (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) :
    Challenge.sgn (Challenge.pSand r (Challenge.triHalf n r 0) (Challenge.triHalf n r 1) *
      Challenge.pSand r (Challenge.triHalf n r 1) (Challenge.triHalf n r 2) *
      Challenge.pSand r (Challenge.triHalf n r 2) (Challenge.triHalf n r 0)) = 1 := by
  rw [pSand_01 n r hr hn hpar, pSand_12 n r hr hn hpar,
    pSand_20 n r hr hn hpar, one_mul, one_mul]
  exact SignSmall.sgn_swap12 (by rcases hr with rfl | rfl <;> omega)

/-- Every clause of the frozen triangle lemma on the actual frozen half-diagrams. -/
theorem check_Lemma52 : Challenge.Lemma52 := by
  intro n r hr hn hpar
  exact ⟨BrauerTriangleBasics.triHalf_mem_hr n r hr hn hpar,
    compat_01 n r hr hn, compat_12 n r hr hn, compat_20 n r hr hn,
    pSand_01 n r hr hn hpar, pSand_12 n r hr hn hpar, pSand_20 n r hr hn hpar,
    triangle_sign n r hr hn hpar⟩

end CodexPaper5.BrauerTriangle

#print axioms CodexPaper5.BrauerTriangle.nextIndex
#print axioms CodexPaper5.BrauerTriangle.freeLabel
#print axioms CodexPaper5.BrauerTriangle.freeLabel_lt
#print axioms CodexPaper5.BrauerTriangle.freePoint
#print axioms CodexPaper5.BrauerTriangle.freePoint_mem
#print axioms CodexPaper5.BrauerTriangle.pos_freePoint
#print axioms CodexPaper5.BrauerTriangle.triPartner_pos
#print axioms CodexPaper5.BrauerTriangle.reachable_via_zero
#print axioms CodexPaper5.BrauerTriangle.compat_01
#print axioms CodexPaper5.BrauerTriangle.compat_12
#print axioms CodexPaper5.BrauerTriangle.compat_20
#print axioms CodexPaper5.BrauerTriangle.compat_next
#print axioms CodexPaper5.BrauerTriangle.expectedSand
#print axioms CodexPaper5.BrauerTriangle.freePoint_reachable
#print axioms CodexPaper5.BrauerTriangle.pSand_next
#print axioms CodexPaper5.BrauerTriangle.pSand_01
#print axioms CodexPaper5.BrauerTriangle.pSand_12
#print axioms CodexPaper5.BrauerTriangle.pSand_20
#print axioms CodexPaper5.BrauerTriangle.triangle_sign
#print axioms CodexPaper5.BrauerTriangle.check_Lemma52
