import Research.Backfill.Paper5.Proof.DiagramRanksOccurring

set_option autoImplicit false

namespace CodexPaper5.BrauerJoinSplice

open BackfillPaper5

/-- Exchange A and Z, act by q on R, and fix every other actual point. -/
def spliceMatching {n : ℕ} (A Z R : Finset (Fin n)) (e : ↥A ≃ ↥Z)
    (q : ↥R → ↥R) (a : Fin n) : Fin n :=
  if ha : a ∈ A then (e ⟨a, ha⟩).val
  else if hz : a ∈ Z then (e.symm ⟨a, hz⟩).val
  else if hr : a ∈ R then (q ⟨a, hr⟩).val
  else a

theorem spliceMatching_on_A {n : ℕ} (A Z R : Finset (Fin n)) (e : ↥A ≃ ↥Z)
    (q : ↥R → ↥R) {a : Fin n} (ha : a ∈ A) :
    spliceMatching A Z R e q a = (e ⟨a, ha⟩).val := by
  simp only [spliceMatching, dite_eq_left ha]

theorem spliceMatching_on_Z {n : ℕ} (A Z R : Finset (Fin n)) (e : ↥A ≃ ↥Z)
    (q : ↥R → ↥R) (hAZ : Disjoint A Z) {a : Fin n} (ha : a ∈ Z) :
    spliceMatching A Z R e q a = (e.symm ⟨a, ha⟩).val := by
  have hnA : a ∉ A := Finset.disjoint_right.mp hAZ ha
  simp only [spliceMatching, dite_eq_right hnA, dite_eq_left ha]

theorem spliceMatching_on_R {n : ℕ} (A Z R : Finset (Fin n)) (e : ↥A ≃ ↥Z)
    (q : ↥R → ↥R) (hAR : Disjoint A R) (hZR : Disjoint Z R)
    {a : Fin n} (ha : a ∈ R) : spliceMatching A Z R e q a = (q ⟨a, ha⟩).val := by
  have hnA : a ∉ A := Finset.disjoint_right.mp hAR ha
  have hnZ : a ∉ Z := Finset.disjoint_right.mp hZR ha
  simp only [spliceMatching, dite_eq_right hnA, dite_eq_right hnZ, dite_eq_left ha]

theorem spliceMatching_outside {n : ℕ} (A Z R : Finset (Fin n)) (e : ↥A ≃ ↥Z)
    (q : ↥R → ↥R) {a : Fin n} (hA : a ∉ A) (hZ : a ∉ Z) (hR : a ∉ R) :
    spliceMatching A Z R e q a = a := by
  simp only [spliceMatching, dite_eq_right hA, dite_eq_right hZ, dite_eq_right hR]

/-- Both inverse laws for e and the actual q involution give a whole-domain involution. -/
theorem spliceMatching_involutive {n : ℕ} (A Z R : Finset (Fin n)) (e : ↥A ≃ ↥Z)
    (q : ↥R → ↥R) (hAZ : Disjoint A Z) (hAR : Disjoint A R) (hZR : Disjoint Z R)
    (hq : Function.Involutive q) : Function.Involutive (spliceMatching A Z R e q) := by
  intro a
  by_cases hA : a ∈ A
  · let c : ↥A := ⟨a, hA⟩
    have hZ : (e c).val ∈ Z := (e c).property
    rw [spliceMatching_on_A A Z R e q hA,
      spliceMatching_on_Z A Z R e q hAZ hZ]
    exact congrArg Subtype.val (e.symm_apply_apply c)
  · by_cases hZ : a ∈ Z
    · let c : ↥Z := ⟨a, hZ⟩
      have hA' : (e.symm c).val ∈ A := (e.symm c).property
      rw [spliceMatching_on_Z A Z R e q hAZ hZ,
        spliceMatching_on_A A Z R e q hA']
      exact congrArg Subtype.val (e.apply_symm_apply c)
    · by_cases hR : a ∈ R
      · let c : ↥R := ⟨a, hR⟩
        have hR' : (q c).val ∈ R := (q c).property
        rw [spliceMatching_on_R A Z R e q hAR hZR hR,
          spliceMatching_on_R A Z R e q hAR hZR hR']
        exact congrArg Subtype.val (hq c)
      · have hf := spliceMatching_outside A Z R e q hA hZ hR
        simp only [hf]

theorem spliceMatching_ne_on_A {n : ℕ} (A Z R : Finset (Fin n)) (e : ↥A ≃ ↥Z)
    (q : ↥R → ↥R) (hAZ : Disjoint A Z) {a : Fin n} (ha : a ∈ A) :
    spliceMatching A Z R e q a ≠ a := by
  intro heq
  have hz : spliceMatching A Z R e q a ∈ Z := by
    rw [spliceMatching_on_A A Z R e q ha]
    exact (e ⟨a, ha⟩).property
  exact (Finset.disjoint_left.mp hAZ ha) (heq ▸ hz)

theorem spliceMatching_ne_on_Z {n : ℕ} (A Z R : Finset (Fin n)) (e : ↥A ≃ ↥Z)
    (q : ↥R → ↥R) (hAZ : Disjoint A Z) {a : Fin n} (ha : a ∈ Z) :
    spliceMatching A Z R e q a ≠ a := by
  intro heq
  have hA : spliceMatching A Z R e q a ∈ A := by
    rw [spliceMatching_on_Z A Z R e q hAZ ha]
    exact (e.symm ⟨a, ha⟩).property
  exact (Finset.disjoint_right.mp hAZ ha) (heq ▸ hA)

theorem spliceMatching_ne_on_R {n : ℕ} (A Z R : Finset (Fin n)) (e : ↥A ≃ ↥Z)
    (q : ↥R → ↥R) (hAR : Disjoint A R) (hZR : Disjoint Z R)
    (hq : ∀ a : ↥R, q a ≠ a) {a : Fin n} (ha : a ∈ R) :
    spliceMatching A Z R e q a ≠ a := by
  intro heq
  let c : ↥R := ⟨a, ha⟩
  have hv : (q c).val = c.val :=
    (spliceMatching_on_R A Z R e q hAR hZR ha).symm.trans heq
  exact hq c (Subtype.ext hv)

/-- Every point in the three actual moving blocks is nonfixed. -/
theorem spliceMatching_ne_of_mem {n : ℕ} (A Z R : Finset (Fin n)) (e : ↥A ≃ ↥Z)
    (q : ↥R → ↥R) (hAZ : Disjoint A Z) (hAR : Disjoint A R) (hZR : Disjoint Z R)
    (hq : ∀ a : ↥R, q a ≠ a) {a : Fin n} (ha : a ∈ A ∨ a ∈ Z ∨ a ∈ R) :
    spliceMatching A Z R e q a ≠ a := by
  rcases ha with ha | ha | ha
  · exact spliceMatching_ne_on_A A Z R e q hAZ ha
  · exact spliceMatching_ne_on_Z A Z R e q hAZ ha
  · exact spliceMatching_ne_on_R A Z R e q hAR hZR hq ha

theorem spliceMatching_fixed_of_disjoint {n : ℕ} (F A Z R : Finset (Fin n))
    (e : ↥A ≃ ↥Z) (q : ↥R → ↥R) (hFA : Disjoint F A) (hFZ : Disjoint F Z)
    (hFR : Disjoint F R) {a : Fin n} (ha : a ∈ F) :
    spliceMatching A Z R e q a = a :=
  spliceMatching_outside A Z R e q
    (Finset.disjoint_left.mp hFA ha) (Finset.disjoint_left.mp hFZ ha)
    (Finset.disjoint_left.mp hFR ha)

/-- The real Half is legal once its whole nonfree set is covered by the three moving blocks. -/
theorem spliceHalf_mem_hr {n r : ℕ} (F A Z R : Finset (Fin n)) (e : ↥A ≃ ↥Z)
    (q : ↥R → ↥R) (hF : F.card = r) (hAZ : Disjoint A Z) (hAR : Disjoint A R)
    (hZR : Disjoint Z R) (hFA : Disjoint F A) (hFZ : Disjoint F Z) (hFR : Disjoint F R)
    (hcover : ∀ a : Fin n, a ∉ F → a ∈ A ∨ a ∈ Z ∨ a ∈ R)
    (hqI : Function.Involutive q) (hqN : ∀ a : ↥R, q a ≠ a) :
    (F, spliceMatching A Z R e q) ∈ Challenge.Hr Challenge.Fam.B n r := by
  refine ⟨hF, spliceMatching_involutive A Z R e q hAZ hAR hZR hqI, ?_, ?_⟩
  · intro a ha
    exact spliceMatching_fixed_of_disjoint F A Z R e q hFA hFZ hFR ha
  · intro _hB a ha
    exact spliceMatching_ne_of_mem A Z R e q hAZ hAR hZR hqN (hcover a ha)

#print axioms CodexPaper5.BrauerJoinSplice.spliceMatching
#print axioms CodexPaper5.BrauerJoinSplice.spliceMatching_on_A
#print axioms CodexPaper5.BrauerJoinSplice.spliceMatching_on_Z
#print axioms CodexPaper5.BrauerJoinSplice.spliceMatching_on_R
#print axioms CodexPaper5.BrauerJoinSplice.spliceMatching_outside
#print axioms CodexPaper5.BrauerJoinSplice.spliceMatching_involutive
#print axioms CodexPaper5.BrauerJoinSplice.spliceMatching_ne_on_A
#print axioms CodexPaper5.BrauerJoinSplice.spliceMatching_ne_on_Z
#print axioms CodexPaper5.BrauerJoinSplice.spliceMatching_ne_on_R
#print axioms CodexPaper5.BrauerJoinSplice.spliceMatching_ne_of_mem
#print axioms CodexPaper5.BrauerJoinSplice.spliceMatching_fixed_of_disjoint
#print axioms CodexPaper5.BrauerJoinSplice.spliceHalf_mem_hr

end CodexPaper5.BrauerJoinSplice
