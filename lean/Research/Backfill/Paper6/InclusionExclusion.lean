import Research.Backfill.Paper6.ChallengeV3

/-!
# Integer inclusion–exclusion for arbitrary binary monomial families

Candidate source only: no compilation or acceptance has been performed for this
module. The final declaration has exactly the frozen V3.Lem21 type. All dimensions,
family sizes, repeated variable sets, and empty sets are allowed. In particular,
there is no nonemptiness assumption on the family or on its monomials.
-/

set_option autoImplicit false

namespace Paper6InclusionExclusion

open Finset
open BackfillPaper6.V3

/-- The integer 0/1 value of a binary field element. -/
def bit (z : ZMod 2) : ℤ := if z = 1 then 1 else 0

/-- The additive character written without division. -/
def character (z : ZMod 2) : ℤ := 1 + (-2) * bit z

theorem bit_mul (a b : ZMod 2) : bit (a * b) = bit a * bit b := by
  revert a b
  decide

theorem character_add (a b : ZMod 2) :
    character (a + b) = character a * character b := by
  revert a b
  decide

theorem binary_mul_one_iff (a b : ZMod 2) :
    a * b = 1 ↔ a = 1 ∧ b = 1 := by
  revert a b
  decide

theorem sum_bit : (∑ z : ZMod 2, bit z) = 1 := by decide

theorem bit_prod {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ZMod 2) :
    bit (∏ i ∈ s, f i) = ∏ i ∈ s, bit (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [bit]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, bit_mul, ih]

theorem character_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ZMod 2) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [character, bit]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, character_add, ih]

theorem binary_prod_one_iff {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ZMod 2) :
    (∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, binary_mul_one_iff, ih]
      constructor
      · rintro ⟨haone, hsone⟩ i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact haone
        · exact hsone i hi
      · intro h
        exact ⟨h a (Finset.mem_insert_self a s),
          fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

/-- Over the binary field, Hamming weight is the sum of the integer bits. -/
theorem weight_as_sum {α : Type*} [Fintype α] (f : α → ZMod 2) :
    (hammingNorm f : ℤ) = ∑ x, bit (f x) := by
  classical
  have hz : ∀ z : ZMod 2, z ≠ 0 ↔ z = 1 := by decide
  simp only [hammingNorm, bit, Finset.sum_boole, hz]

/-- Repeated factors in overlapping variable sets are harmless for binary values. -/
theorem monomial_product (m k : ℕ) (S : Fin k → Finset (Fin m))
    (T : Finset (Fin k)) (x : Pt m) :
    (∏ i ∈ T, bit (∏ j ∈ S i, x j)) =
      ∏ j ∈ T.biUnion S, bit (x j) := by
  rw [← bit_prod T (fun i => ∏ j ∈ S i, x j), ← bit_prod (T.biUnion S) x]
  have hone : (∏ i ∈ T, ∏ j ∈ S i, x j) = 1 ↔
      (∏ j ∈ T.biUnion S, x j) = 1 := by
    simp only [binary_prod_one_iff]
    constructor
    · intro h j hj
      obtain ⟨i, hiT, hjS⟩ := Finset.mem_biUnion.mp hj
      exact h i hiT j hjS
    · intro h i hiT j hjS
      exact h j (Finset.mem_biUnion.mpr ⟨i, hiT, hjS⟩)
  simp only [bit, hone]

/-- Fixing the coordinates in U to one leaves exactly m-card(U) free binary coordinates.
This is proved by finite product/sum distributivity, without enumerating the points. -/
theorem sum_coordinate_product (m : ℕ) (U : Finset (Fin m)) :
    (∑ x : Pt m, ∏ j ∈ U, bit (x j)) = (2 : ℤ) ^ (m - U.card) := by
  classical
  let g : Fin m → ZMod 2 → ℤ := fun j z => if j ∈ U then bit z else 1
  have hpoint (x : Pt m) :
      (∏ j ∈ U, bit (x j)) = ∏ j : Fin m, g j (x j) := by
    simpa only [g] using (Finset.prod_ite_mem_eq U (fun j => bit (x j))).symm
  have hcolumn (j : Fin m) : (∑ z : ZMod 2, g j z) = if j ∈ U then 1 else 2 := by
    by_cases hj : j ∈ U
    · simp only [g, ite_eq_left hj, sum_bit]
    · simp [g, hj]
  calc
    (∑ x : Pt m, ∏ j ∈ U, bit (x j)) =
        ∑ x : Pt m, ∏ j : Fin m, g j (x j) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact hpoint x
    _ = ∏ j : Fin m, ∑ z : ZMod 2, g j z := (Fintype.prod_sum g).symm
    _ = ∏ j : Fin m, if j ∈ U then (1 : ℤ) else 2 := by
      apply Finset.prod_congr rfl
      intro j _hj
      exact hcolumn j
    _ = ∏ j : Fin m, if j ∈ Uᶜ then (2 : ℤ) else 1 := by
      apply Finset.prod_congr rfl
      intro j _hj
      by_cases hj : j ∈ U <;> simp [hj]
    _ = ∏ _j ∈ Uᶜ, (2 : ℤ) := Finset.prod_ite_mem_eq Uᶜ (fun _ => (2 : ℤ))
    _ = (2 : ℤ) ^ (m - U.card) := by simp [Finset.card_compl]

/-- Finite distributivity expands the binary additive character over all subsets. -/
theorem character_expansion (k : ℕ) (f : Fin k → ZMod 2) :
    character (∑ i, f i) =
      ∑ T : Finset (Fin k), (-2 : ℤ) ^ T.card * ∏ i ∈ T, bit (f i) := by
  rw [character_sum]
  change (∏ i : Fin k, (1 + (-2 : ℤ) * bit (f i))) = _
  rw [Finset.prod_one_add, Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro T _hT
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The exact frozen arbitrary-dimension, arbitrary-family inclusion–exclusion formula. -/
theorem check_Lem21 : BackfillPaper6.V3.Lem21 := by
  classical
  intro m k S
  let F : Pt m → ZMod 2 := fun x => ∑ i, ∏ j ∈ S i, x j
  let E : Finset (Finset (Fin k)) := Finset.univ.filter (fun T => T.Nonempty)
  let coeff : Finset (Fin k) → ℤ := fun T =>
    (-2 : ℤ) ^ T.card * (2 : ℤ) ^ (m - (T.biUnion S).card)
  let reduced : Finset (Fin k) → ℤ := fun T =>
    (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^ (m - (T.biUnion S).card)
  change (hammingNorm F : ℤ) = ∑ T ∈ E, reduced T
  have hchar : (∑ x : Pt m, character (F x)) =
      (2 : ℤ) ^ m + (-2) * (hammingNorm F : ℤ) := by
    calc
      (∑ x : Pt m, character (F x)) =
          (∑ _x : Pt m, (1 : ℤ)) + (-2) * ∑ x : Pt m, bit (F x) := by
        simp only [character, Finset.sum_add_distrib, Finset.mul_sum]
      _ = (2 : ℤ) ^ m + (-2) * (hammingNorm F : ℤ) := by
        rw [← weight_as_sum F]
        simp [Pt]
  have hsum : (2 : ℤ) ^ m + (-2) * (hammingNorm F : ℤ) =
      ∑ T : Finset (Fin k), coeff T := by
    calc
      (2 : ℤ) ^ m + (-2) * (hammingNorm F : ℤ) =
          ∑ x : Pt m, character (F x) := hchar.symm
      _ = ∑ x : Pt m, ∑ T : Finset (Fin k),
          (-2 : ℤ) ^ T.card * ∏ i ∈ T, bit (∏ j ∈ S i, x j) := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact character_expansion k (fun i => ∏ j ∈ S i, x j)
      _ = ∑ T : Finset (Fin k), (-2 : ℤ) ^ T.card *
          ∑ x : Pt m, ∏ i ∈ T, bit (∏ j ∈ S i, x j) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = ∑ T : Finset (Fin k), coeff T := by
        apply Finset.sum_congr rfl
        intro T _hT
        dsimp only [coeff]
        congr 1
        calc
          (∑ x : Pt m, ∏ i ∈ T, bit (∏ j ∈ S i, x j)) =
              ∑ x : Pt m, ∏ j ∈ T.biUnion S, bit (x j) := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact monomial_product m k S T x
          _ = (2 : ℤ) ^ (m - (T.biUnion S).card) :=
            sum_coordinate_product m (T.biUnion S)
  have hE : E = (Finset.univ : Finset (Finset (Fin k))).erase ∅ := by
    ext T
    simp [E, Finset.nonempty_iff_ne_empty]
  have hempty : coeff ∅ = (2 : ℤ) ^ m := by simp [coeff]
  have hsplit := Finset.add_sum_erase
    (Finset.univ : Finset (Finset (Fin k))) coeff (a := ∅) (Finset.mem_univ _)
  rw [← hE, hempty] at hsplit
  have hfactor : (∑ T ∈ E, coeff T) = (-2) * ∑ T ∈ E, reduced T := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    have hnonempty : T.Nonempty := (Finset.mem_filter.mp hT).2
    have hpositive : 0 < T.card := Finset.card_pos.mpr hnonempty
    have hpow : (-2 : ℤ) ^ T.card = (-2) * (-2 : ℤ) ^ (T.card - 1) := by
      calc
        (-2 : ℤ) ^ T.card = (-2 : ℤ) ^ ((T.card - 1) + 1) :=
          congrArg (fun n : ℕ => (-2 : ℤ) ^ n) (by omega)
        _ = (-2) * (-2 : ℤ) ^ (T.card - 1) := by rw [pow_succ]; ring
    dsimp only [coeff, reduced]
    rw [hpow]
    ring
  rw [← hsplit, hfactor] at hsum
  linarith [hsum]

end Paper6InclusionExclusion

#print axioms Paper6InclusionExclusion.bit_mul
#print axioms Paper6InclusionExclusion.character_add
#print axioms Paper6InclusionExclusion.binary_mul_one_iff
#print axioms Paper6InclusionExclusion.sum_bit
#print axioms Paper6InclusionExclusion.bit_prod
#print axioms Paper6InclusionExclusion.character_sum
#print axioms Paper6InclusionExclusion.binary_prod_one_iff
#print axioms Paper6InclusionExclusion.weight_as_sum
#print axioms Paper6InclusionExclusion.monomial_product
#print axioms Paper6InclusionExclusion.sum_coordinate_product
#print axioms Paper6InclusionExclusion.character_expansion
#print axioms Paper6InclusionExclusion.check_Lem21
