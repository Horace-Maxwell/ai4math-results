import Research.Backfill.Paper7.MomentB6ComputableKernel

/-! Uncompiled universal weighted reindexing, no concrete numerical candidate.
The actual861/863 decode equivalence identifies accepted (B,c) with all sorted
(c,a,A-c-a) of sum A. Arbitrary F carries every guard, multiplicity and genuine
q weight unchanged. The final specialization replaces original B membership by
arithmetic bounds/parity Bool decisions. No performance claim or option change. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6SortedLeftCRange (A : ℕ) : Finset ℕ :=
  Finset.Icc ((A+2)/3) A
#print axioms Paper7MomentCounts.b6SortedLeftCRange

def b6SortedLeftARange (A c : ℕ) : Finset ℕ :=
  Finset.Icc ((A-c+1)/2) (min c (A-c))
#print axioms Paper7MomentCounts.b6SortedLeftARange

def b6SortedLeftLow (A c a : ℕ) : ℕ := A-c-a
#print axioms Paper7MomentCounts.b6SortedLeftLow

def b6SortedLeftSquares (A c a : ℕ) : ℕ :=
  c^2+a^2+(b6SortedLeftLow A c a)^2
#print axioms Paper7MomentCounts.b6SortedLeftSquares

theorem b6SortedLeftWindow_iff (A c a : ℕ) :
    c ∈ b6SortedLeftCRange A ∧ a ∈ b6SortedLeftARange A c ↔
      b6SortedLeftLow A c a ≤ a ∧ a ≤ c ∧ c+a+b6SortedLeftLow A c a = A := by
  simp only [b6SortedLeftCRange, b6SortedLeftARange, b6SortedLeftLow,
    Finset.mem_Icc, le_min_iff]
  omega
#print axioms Paper7MomentCounts.b6SortedLeftWindow_iff

theorem b6SortedLeftCoordinates_of_accept (A B c : ℕ)
    (h : b6EvalSortedAccept A B c = true) :
    c ∈ b6SortedLeftCRange A ∧
      b6EvalHigh A B c ∈ b6SortedLeftARange A c ∧
      b6SortedLeftLow A c (b6EvalHigh A B c) = b6EvalLow A B c ∧
      b6SortedLeftSquares A c (b6EvalHigh A B c) = B := by
  have hs : b6EvalLow A B c ≤ b6EvalHigh A B c ∧
      b6EvalHigh A B c ≤ c ∧
      c+b6EvalHigh A B c+b6EvalLow A B c = A ∧
      c^2+(b6EvalHigh A B c)^2+(b6EvalLow A B c)^2 = B := by
    simpa only [b6EvalHigh_eq, b6EvalLow_eq] using
      labelled_sorted_triple_decode_sound A B c ((b6EvalSortedAccept_iff A B c).mp h)
  have hl : b6SortedLeftLow A c (b6EvalHigh A B c) = b6EvalLow A B c := by
    unfold b6SortedLeftLow
    omega
  have hw := (b6SortedLeftWindow_iff A c (b6EvalHigh A B c)).mpr
    (by rw [hl]; exact ⟨hs.1, hs.2.1, hs.2.2.1⟩)
  refine ⟨hw.1, hw.2, hl, ?_⟩
  unfold b6SortedLeftSquares
  rw [hl]
  exact hs.2.2.2
#print axioms Paper7MomentCounts.b6SortedLeftCoordinates_of_accept

theorem b6SortedLeftCoordinates_decode (A c a : ℕ)
    (hc : c ∈ b6SortedLeftCRange A) (ha : a ∈ b6SortedLeftARange A c) :
    c ∈ b6EvalScalarRange A (b6SortedLeftSquares A c a) ∧
      b6EvalSortedAccept A (b6SortedLeftSquares A c a) c = true ∧
      b6EvalHigh A (b6SortedLeftSquares A c a) c = a ∧
      b6EvalLow A (b6SortedLeftSquares A c a) c = b6SortedLeftLow A c a := by
  have hw := (b6SortedLeftWindow_iff A c a).mp ⟨hc,ha⟩
  have hd := labelled_sorted_triple_decode_complete A (b6SortedLeftSquares A c a)
    c a (b6SortedLeftLow A c a) hw.1 hw.2.1 hw.2.2 rfl
  refine ⟨?_, (b6EvalSortedAccept_iff A (b6SortedLeftSquares A c a) c).mpr hd.2.1, ?_, ?_⟩
  · simpa only [b6EvalScalarRange_eq] using hd.1
  · simpa only [b6EvalHigh_eq] using hd.2.2.1
  · simpa only [b6EvalLow_eq] using hd.2.2.2
#print axioms Paper7MomentCounts.b6SortedLeftCoordinates_decode

theorem b6SortedLeftWeightedReindex (A : ℕ) (s : Finset ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → ℤ) :
    (∑ B ∈ s, ∑ c ∈ b6EvalScalarRange A B,
      bif b6EvalSortedAccept A B c then F B c (b6EvalHigh A B c) (b6EvalLow A B c) else 0) =
    ∑ c ∈ b6SortedLeftCRange A, ∑ a ∈ b6SortedLeftARange A c,
      bif decide (b6SortedLeftSquares A c a ∈ s) then
        F (b6SortedLeftSquares A c a) c a (b6SortedLeftLow A c a) else 0 := by
  classical
  let D : Finset (Σ _ : ℕ, ℕ) :=
    s.sigma (fun B => (b6EvalScalarRange A B).filter (fun c => b6EvalSortedAccept A B c = true))
  let E : Finset (Σ _ : ℕ, ℕ) :=
    (b6SortedLeftCRange A).sigma (fun c =>
      (b6SortedLeftARange A c).filter (fun a => b6SortedLeftSquares A c a ∈ s))
  have hD (u : Σ _ : ℕ, ℕ) : u ∈ D ↔
      u.1 ∈ s ∧ u.2 ∈ b6EvalScalarRange A u.1 ∧ b6EvalSortedAccept A u.1 u.2 = true := by
    simp only [D, Finset.mem_sigma, Finset.mem_filter]
  have hE (v : Σ _ : ℕ, ℕ) : v ∈ E ↔
      v.1 ∈ b6SortedLeftCRange A ∧ v.2 ∈ b6SortedLeftARange A v.1 ∧
        b6SortedLeftSquares A v.1 v.2 ∈ s := by
    simp only [E, Finset.mem_sigma, Finset.mem_filter]
  have hmap (u : Σ _ : ℕ, ℕ) (hu : u ∈ D) :
      (⟨u.2, b6EvalHigh A u.1 u.2⟩ : Σ _ : ℕ, ℕ) ∈ E := by
    have hd := (hD u).mp hu
    have hc := b6SortedLeftCoordinates_of_accept A u.1 u.2 hd.2.2
    apply (hE _).mpr
    exact ⟨hc.1,hc.2.1,by simpa only [hc.2.2.2] using hd.1⟩
  have hinv (v : Σ _ : ℕ, ℕ) (hv : v ∈ E) :
      (⟨b6SortedLeftSquares A v.1 v.2, v.1⟩ : Σ _ : ℕ, ℕ) ∈ D := by
    have he := (hE v).mp hv
    have hd := b6SortedLeftCoordinates_decode A v.1 v.2 he.1 he.2.1
    exact (hD _).mpr ⟨he.2.2,hd.1,hd.2.1⟩
  have hleft (u : Σ _ : ℕ, ℕ) (hu : u ∈ D) :
      (⟨b6SortedLeftSquares A u.2 (b6EvalHigh A u.1 u.2), u.2⟩ : Σ _ : ℕ, ℕ) = u := by
    have hc := b6SortedLeftCoordinates_of_accept A u.1 u.2 ((hD u).mp hu).2.2
    rcases u with ⟨B,c⟩
    change (⟨b6SortedLeftSquares A c (b6EvalHigh A B c), c⟩ : Σ _ : ℕ, ℕ) = ⟨B,c⟩
    rw [hc.2.2.2]
  have hright (v : Σ _ : ℕ, ℕ) (hv : v ∈ E) :
      (⟨v.1,b6EvalHigh A (b6SortedLeftSquares A v.1 v.2) v.1⟩ : Σ _ : ℕ, ℕ) = v := by
    have he := (hE v).mp hv
    have hd := b6SortedLeftCoordinates_decode A v.1 v.2 he.1 he.2.1
    rcases v with ⟨c,a⟩
    change (⟨c,b6EvalHigh A (b6SortedLeftSquares A c a) c⟩ : Σ _ : ℕ, ℕ) = ⟨c,a⟩
    rw [hd.2.2.1]
  have hsum :
      (∑ u ∈ D, F u.1 u.2 (b6EvalHigh A u.1 u.2) (b6EvalLow A u.1 u.2)) =
        ∑ v ∈ E, F (b6SortedLeftSquares A v.1 v.2) v.1 v.2 (b6SortedLeftLow A v.1 v.2) := by
    refine Finset.sum_bij'
      (fun u _ => (⟨u.2,b6EvalHigh A u.1 u.2⟩ : Σ _ : ℕ, ℕ))
      (fun v _ => (⟨b6SortedLeftSquares A v.1 v.2,v.1⟩ : Σ _ : ℕ, ℕ))
      hmap hinv hleft hright ?_
    intro u hu
    have hc := b6SortedLeftCoordinates_of_accept A u.1 u.2 ((hD u).mp hu).2.2
    change F u.1 u.2 (b6EvalHigh A u.1 u.2) (b6EvalLow A u.1 u.2) =
      F (b6SortedLeftSquares A u.2 (b6EvalHigh A u.1 u.2)) u.2
        (b6EvalHigh A u.1 u.2) (b6SortedLeftLow A u.2 (b6EvalHigh A u.1 u.2))
    rw [hc.2.2.2,hc.2.2.1]
  calc
    _ = ∑ u ∈ D, F u.1 u.2 (b6EvalHigh A u.1 u.2) (b6EvalLow A u.1 u.2) := by
      simp only [D, Finset.sum_sigma, Finset.sum_filter, Bool.cond_eq_ite]
    _ = ∑ v ∈ E, F (b6SortedLeftSquares A v.1 v.2) v.1 v.2 (b6SortedLeftLow A v.1 v.2) := hsum
    _ = _ := by
      simp only [E, Finset.sum_sigma, Finset.sum_filter, Bool.cond_eq_ite, decide_eq_true_eq]
#print axioms Paper7MomentCounts.b6SortedLeftWeightedReindex

def b6SortedLeftBGuard (Z R A B : ℕ) : Bool :=
  decide (max ((A^2+2)/3) (R-(Z-A)^2) ≤ B) &&
    decide (B ≤ min (A^2) (R-((Z-A)^2+2)/3)) && decide (B%2=A%2)
#print axioms Paper7MomentCounts.b6SortedLeftBGuard

theorem b6SortedLeftBGuard_iff (Z R A B : ℕ) :
    b6SortedLeftBGuard Z R A B = true ↔ B ∈ b6EvalBRange Z R A := by
  simp only [b6SortedLeftBGuard, b6EvalBRange, Finset.mem_filter, Finset.mem_Icc,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc]
#print axioms Paper7MomentCounts.b6SortedLeftBGuard_iff

theorem b6SortedLeftWeightedBSupport (Z R A : ℕ)
    (F : ℕ → ℕ → ℕ → ℕ → ℤ) :
    (∑ B ∈ b6EvalBRange Z R A, ∑ c ∈ b6EvalScalarRange A B,
      bif b6EvalSortedAccept A B c then F B c (b6EvalHigh A B c) (b6EvalLow A B c) else 0) =
    ∑ c ∈ b6SortedLeftCRange A, ∑ a ∈ b6SortedLeftARange A c,
      bif b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) then
        F (b6SortedLeftSquares A c a) c a (b6SortedLeftLow A c a) else 0 := by
  classical
  rw [b6SortedLeftWeightedReindex]
  apply Finset.sum_congr rfl
  intro c _hc
  apply Finset.sum_congr rfl
  intro a _ha
  simp only [Bool.cond_eq_ite]
  by_cases h : b6SortedLeftSquares A c a ∈ b6EvalBRange Z R A
  · rw [ite_eq_left (decide_eq_true h),
      ite_eq_left ((b6SortedLeftBGuard_iff Z R A (b6SortedLeftSquares A c a)).mpr h)]
  · rw [ite_eq_right (fun ht => h (of_decide_eq_true ht)),
      ite_eq_right (fun ht => h ((b6SortedLeftBGuard_iff Z R A (b6SortedLeftSquares A c a)).mp ht))]
#print axioms Paper7MomentCounts.b6SortedLeftWeightedBSupport

end Paper7MomentCounts
