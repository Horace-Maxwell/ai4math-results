import Research.Backfill.Paper7.RootDomainCoverage

/-! A kernel-checkable search with exact sum pruning and a forced final root.
Each node may be certified separately; no external search result is assumed. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

theorem root_sum_bounds (a : List ℤ) (lo : ℤ)
    (h : ∀ z ∈ a, lo ≤ z ∧ z ≤ 9) :
    (a.length : ℤ) * lo ≤ a.sum ∧ a.sum ≤ (a.length : ℤ) * 9 := by
  induction a with
  | nil => simp
  | cons z a ih =>
    have hz := h z (by simp)
    have ht := ih (fun w hw => h w (List.mem_cons_of_mem z hw))
    simp only [List.length_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith
#print axioms Paper7CycleThreeCertificate.root_sum_bounds

/-- At depth1 the zero-sum condition determines the last root. At larger
depths a sum interval may reject a whole branch, otherwise all19 choices remain. -/
def prunedRootCheck (rows : List (List ℤ)) (pref : List ℤ) : ℕ → ℤ → Bool
  | 0, _ => rootLeafCheck rows pref
  | 1, lo =>
    let z := -pref.sum
    if lo ≤ z ∧ -9 ≤ z ∧ z ≤ 9 then rootLeafCheck rows (pref ++ [z]) else true
  | n + 2, lo =>
    if 0 < pref.sum + ((n + 2 : ℕ) : ℤ) * lo ∨
        pref.sum + ((n + 2 : ℕ) : ℤ) * 9 < 0 then
      true
    else rootChoices.all (fun z => if lo ≤ z then
      prunedRootCheck rows (pref ++ [z]) (n + 1) z else true)
#print axioms Paper7CycleThreeCertificate.prunedRootCheck

theorem prunedRootCheck_sound (rows : List (List ℤ)) (pref : List ℤ)
    (n : ℕ) (lo : ℤ) (hcheck : prunedRootCheck rows pref n lo = true)
    (a : List ℤ) (hlen : a.length = n) (hsort : a.Pairwise (· ≤ ·))
    (hrange : ∀ z ∈ a, -9 ≤ z ∧ z ≤ 9) (hlower : ∀ z ∈ a, lo ≤ z)
    (hpattern : rootPattern (pref ++ a)) : pref ++ a ∈ rows := by
  induction n using Nat.twoStepInduction generalizing pref lo a with
  | zero =>
    have ha : a = [] := List.length_eq_zero_iff.mp hlen
    subst a
    simpa only [List.append_nil] using
      rootLeafCheck_sound rows pref hcheck (by simpa only [List.append_nil] using hpattern)
  | one =>
    cases a with
    | nil => simp at hlen
    | cons z a =>
      have ha : a = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst a
      have hsum : pref.sum + z = 0 := by
        simpa only [List.sum_append, List.sum_cons, List.sum_nil, add_zero] using hpattern.2.1
      have hz : z = -pref.sum := by omega
      have hzdom : lo ≤ -pref.sum ∧ -9 ≤ -pref.sum ∧ -pref.sum ≤ 9 := by
        simpa only [← hz] using And.intro (hlower z (by simp)) (hrange z (by simp))
      have hleaf : rootLeafCheck rows (pref ++ [-pref.sum]) = true := by
        simpa only [prunedRootCheck, ite_eq_left hzdom] using hcheck
      rw [← hz] at hleaf
      exact rootLeafCheck_sound rows (pref ++ [z]) hleaf hpattern
  | more n _ih0 ih1 =>
    have hb := root_sum_bounds a lo (fun z hz => ⟨hlower z hz, (hrange z hz).2⟩)
    have hsum : pref.sum + a.sum = 0 := by
      simpa only [List.sum_append] using hpattern.2.1
    have hnot : ¬ (0 < pref.sum + ((n + 2 : ℕ) : ℤ) * lo ∨
        pref.sum + ((n + 2 : ℕ) : ℤ) * 9 < 0) := by
      rw [hlen] at hb
      omega
    have hall : rootChoices.all (fun z => if lo ≤ z then
        prunedRootCheck rows (pref ++ [z]) (n + 1) z else true) = true := by
      simpa only [prunedRootCheck, ite_eq_right hnot] using hcheck
    cases a with
    | nil => simp at hlen
    | cons z a =>
      have hpair := List.pairwise_cons.mp hsort
      have hz : z ∈ rootChoices := (mem_rootChoices z).mpr (hrange z (by simp))
      have hloz := hlower z (by simp)
      have hchild : prunedRootCheck rows (pref ++ [z]) (n + 1) z = true := by
        simpa only [ite_eq_left hloz] using List.all_eq_true.mp hall z hz
      have hp : rootPattern ((pref ++ [z]) ++ a) := by
        simpa only [List.append_assoc, List.singleton_append] using hpattern
      have hm := ih1 (pref ++ [z]) z hchild a (by simpa using hlen) hpair.2
        (fun w hw => hrange w (List.mem_cons_of_mem z hw)) hpair.1 hp
      simpa only [List.append_assoc, List.singleton_append] using hm
#print axioms Paper7CycleThreeCertificate.prunedRootCheck_sound

/-- A rejected sum interval is a closed arithmetic certificate for a whole node. -/
theorem prunedRootCheck_prune (rows : List (List ℤ)) (pref : List ℤ)
    (n : ℕ) (lo : ℤ)
    (h : 0 < pref.sum + ((n + 2 : ℕ) : ℤ) * lo ∨
      pref.sum + ((n + 2 : ℕ) : ℤ) * 9 < 0) :
    prunedRootCheck rows pref (n + 2) lo = true := by
  simp only [prunedRootCheck, ite_eq_left h]
#print axioms Paper7CycleThreeCertificate.prunedRootCheck_prune

/-- Every remaining root choice must have a proof. Missing a child cannot
produce the parent proof. This does not evaluate the full parent search. -/
theorem prunedRootCheck_join (rows : List (List ℤ)) (pref : List ℤ)
    (n : ℕ) (lo : ℤ)
    (hchildren : ∀ z ∈ rootChoices, lo ≤ z →
      prunedRootCheck rows (pref ++ [z]) (n + 1) z = true) :
    prunedRootCheck rows pref (n + 2) lo = true := by
  rw [prunedRootCheck]
  split
  · rfl
  · apply List.all_eq_true.mpr
    intro z hz
    by_cases hloz : lo ≤ z
    · simpa only [ite_eq_left hloz] using hchildren z hz hloz
    · simp only [ite_eq_right hloz]
#print axioms Paper7CycleThreeCertificate.prunedRootCheck_join

/-- The finite branching alphabet itself is checked by the kernel. Emitted
parent proofs may split this19-way disjunction and cite child theorems. -/
theorem rootChoices_literal : rootChoices =
    [-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  rfl
#print axioms Paper7CycleThreeCertificate.rootChoices_literal

end Paper7CycleThreeCertificate
