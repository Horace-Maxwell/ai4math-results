import Research.Backfill.Paper7.RootCoefficientRecurrence

/-! Finite root-domain coverage, independent of any generated root table.
The final closed checks against actual future table data are not supplied here. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

/-- Exactly the nineteen integers in the frozen factorization window. -/
def rootChoices : List ℤ := (List.range 19).map (fun k : ℕ => (k : ℤ) - 9)
#print axioms Paper7CycleThreeCertificate.rootChoices

theorem mem_rootChoices (z : ℤ) : z ∈ rootChoices ↔ -9 ≤ z ∧ z ≤ 9 := by
  change z ∈ (List.range 19).map (fun k : ℕ => (k : ℤ) - 9) ↔ -9 ≤ z ∧ z ≤ 9
  constructor
  · intro hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    have hk19 := List.mem_range.mp hk
    omega
  · rintro ⟨hlo, hhi⟩
    have hk : (((z + 9).toNat : ℕ) : ℤ) = z + 9 := Int.toNat_of_nonneg (by omega)
    have hk19 : (z + 9).toNat < 19 := by omega
    apply List.mem_map.mpr
    refine ⟨(z + 9).toNat, List.mem_range.mpr hk19, ?_⟩
    omega
#print axioms Paper7CycleThreeCertificate.mem_rootChoices

def sortedRootLists : ℕ → ℤ → List (List ℤ)
  | 0, _ => [[]]
  | n + 1, lo => rootChoices.flatMap (fun z =>
      if lo ≤ z then (sortedRootLists n z).map (List.cons z) else [])
#print axioms Paper7CycleThreeCertificate.sortedRootLists

theorem sortedRootLists_complete (n : ℕ) (lo : ℤ) (a : List ℤ)
    (hlen : a.length = n) (hsort : a.Pairwise (· ≤ ·))
    (hrange : ∀ z ∈ a, -9 ≤ z ∧ z ≤ 9) (hlower : ∀ z ∈ a, lo ≤ z) :
    a ∈ sortedRootLists n lo := by
  induction n generalizing lo a with
  | zero =>
    have ha : a = [] := List.length_eq_zero_iff.mp hlen
    subst a
    simp [sortedRootLists]
  | succ n ih =>
    cases a with
    | nil => simp at hlen
    | cons z a =>
      have haLen : a.length = n := by simpa using hlen
      have hpair := List.pairwise_cons.mp hsort
      have hz : z ∈ rootChoices := (mem_rootChoices z).mpr (hrange z (by simp))
      have hloz := hlower z (by simp)
      have htail : a ∈ sortedRootLists n z := ih z a haLen hpair.2
        (fun w hw => hrange w (List.mem_cons_of_mem z hw)) hpair.1
      apply List.mem_flatMap.mpr
      refine ⟨z, hz, ?_⟩
      rw [ite_eq_left hloz]
      exact List.mem_map.mpr ⟨a, htail, rfl⟩
#print axioms Paper7CycleThreeCertificate.sortedRootLists_complete

/-- A closed finite Boolean obligation, suitable for independent small prefix
shards. The supplied rows are never assumed to cover the domain. -/
def rootCoverageCheck (rows : List (List ℤ)) (pref : List ℤ) (n : ℕ) (lo : ℤ) : Bool :=
  (sortedRootLists n lo).all (fun a => rootLeafCheck rows (pref ++ a))
#print axioms Paper7CycleThreeCertificate.rootCoverageCheck

theorem rootCoverageCheck_sound (rows : List (List ℤ)) (pref : List ℤ)
    (n : ℕ) (lo : ℤ) (hcheck : rootCoverageCheck rows pref n lo = true)
    (a : List ℤ) (hlen : a.length = n) (hsort : a.Pairwise (· ≤ ·))
    (hrange : ∀ z ∈ a, -9 ≤ z ∧ z ≤ 9) (hlower : ∀ z ∈ a, lo ≤ z)
    (hpattern : rootPattern (pref ++ a)) : pref ++ a ∈ rows := by
  have hmem := sortedRootLists_complete n lo a hlen hsort hrange hlower
  have hleaf := List.all_eq_true.mp hcheck a hmem
  exact rootLeafCheck_sound rows (pref ++ a) hleaf hpattern
#print axioms Paper7CycleThreeCertificate.rootCoverageCheck_sound

/-- Prefix splitting is an exact identity. Future emitted closed certificates
may prove small child checks and combine them without trusting an emitter. -/
theorem rootCoverageCheck_split (rows : List (List ℤ)) (pref : List ℤ)
    (n : ℕ) (lo : ℤ) :
    rootCoverageCheck rows pref (n + 1) lo =
      rootChoices.all (fun z => if lo ≤ z then
        rootCoverageCheck rows (pref ++ [z]) n z else true) := by
  simp only [rootCoverageCheck, sortedRootLists, List.all_flatMap]
  congr 1
  funext z
  by_cases hz : lo ≤ z
  · simp only [ite_eq_left hz, List.all_map]
    congr 1
    funext a
    simp only [List.append_assoc, List.singleton_append]
    rfl
  · simp [hz]
#print axioms Paper7CycleThreeCertificate.rootCoverageCheck_split

end Paper7CycleThreeCertificate
