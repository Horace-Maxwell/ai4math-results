import Research.TaskV.FEI.UpperChallenge

namespace Fei
open Finset Matrix
open scoped BigOperators

private def inc {n : ℕ} (U : Finset (Cube n)) : Matrix (↥U) (↥U) ℝ :=
  fun s t => if s.val ⊆ t.val then 1 else 0

private theorem inc_det {n : ℕ} (U : Finset (Cube n)) : (inc U).det = 1 := by
  classical
  rw [Matrix.det_apply']
  refine (Finset.sum_eq_single 1 ?_ (by simp)).trans ?_
  · intro σ _ hσ
    have hbad : ∃ i : U, ¬ (σ i).val ⊆ i.val := by
      by_contra! h
      apply hσ
      ext i : 1
      refine Subtype.ext <| Finset.eq_of_subset_of_card_le (h i) ?_
      by_contra! hlt
      have hsum := Finset.sum_lt_sum (s := (univ : Finset (↥U)))
        (f := fun j => (σ j).val.card) (g := fun j => j.val.card)
        (fun j _ => Finset.card_le_card (h j)) ⟨i, mem_univ _, hlt⟩
      rw [Equiv.sum_comp σ (fun j : U => j.val.card)] at hsum
      exact (lt_irrefl _ hsum)
    obtain ⟨i, hi⟩ := hbad
    rw [Finset.prod_eq_zero (i := i) (mem_univ _) (by simp [inc, hi]), mul_zero]
  · simp [inc]

private def rowFactor {n : ℕ} (s : Cube n) : ℝ := if s = ∅ then 1 else 2

private theorem entry_factor {n : ℕ} (f : Cube n → Bool)
    (htail : ∀ R : Cube n, ∃ z : ℤ,
      (2 : ℝ)^R.card * (∑ w ∈ support f, if R ⊆ w then coeff f w else 0) =
      (if R = ∅ then (1 : ℝ) else 2) * (z : ℝ)) (s t : Cube n) :
    ∃ z : ℤ, (2 : ℝ)^s.card * (2 : ℝ)^t.card *
      (∑ w ∈ support f, if s ∪ t ⊆ w then coeff f w else 0) = rowFactor s * z := by
  obtain ⟨v, hv⟩ := htail (s ∪ t)
  let gap := s.card + t.card - (s ∪ t).card
  have hg : gap + (s ∪ t).card = s.card + t.card :=
    Nat.sub_add_cancel (Finset.card_union_le _ _)
  rw [← pow_add, ← hg, pow_add, mul_assoc, hv]
  by_cases hu : s ∪ t = ∅
  · have hs := (Finset.union_eq_empty.mp hu).1
    refine ⟨(2 : ℤ)^gap * v, ?_⟩
    rw [show (if s ∪ t = ∅ then (1 : ℝ) else 2) = 1 by simp [hu]]
    simp [rowFactor, hs]
  · by_cases hs : s = ∅
    · refine ⟨(2 : ℤ)^gap * 2 * v, ?_⟩
      rw [show (if s ∪ t = ∅ then (1 : ℝ) else 2) = 2 by simp [hu]]
      simp [hs, rowFactor, mul_assoc]
    · refine ⟨(2 : ℤ)^gap * v, ?_⟩
      push_cast
      simp [hu, hs, rowFactor]
      ring

private theorem row_prod {n : ℕ} (U : Finset (Cube n)) :
    (∏ s : U, rowFactor s.val) = (2 : ℝ)^(U.erase ∅).card := by
  classical
  rw [Finset.prod_coe_sort]
  by_cases h : ∅ ∈ U
  · rw [← Finset.prod_erase_mul _ _ h]
    rw [show rowFactor (∅ : Cube n) = 1 from rfl, mul_one]
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun i hi => by simp [rowFactor, Finset.ne_of_mem_erase hi]
  · rw [Finset.erase_eq_of_notMem h, ← Finset.prod_const]
    exact Finset.prod_congr rfl fun i hi => by
      have hn : i ≠ ∅ := fun he => h (he ▸ hi)
      simp [rowFactor, hn]

theorem upperProduct_of
    (htail : ∀ (n : ℕ) (f : Cube n → Bool) (R : Cube n), ∃ z : ℤ,
      (2 : ℝ)^R.card * (∑ w ∈ support f, if R ⊆ w then coeff f w else 0) =
      (if R = ∅ then (1 : ℝ) else 2) * (z : ℝ)) : UpperProduct := by
  classical
  intro n f U hsub hup
  let a : ↥U → ℝ := fun s => coeff f s.val
  let d : ↥U → ℝ := fun s => (2 : ℝ)^s.val.card
  let r : ↥U → ℝ := fun s => rowFactor s.val
  let B := Matrix.diagonal d * (inc U * Matrix.diagonal a * (inc U).transpose) *
    Matrix.diagonal d
  have hB (s t : U) : B s t = d s * d t *
      (∑ w ∈ U, if s.val ∪ t.val ⊆ w then coeff f w else 0) := by
    dsimp only [B]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    rw [show (∑ w ∈ U, if s.val ∪ t.val ⊆ w then coeff f w else 0) =
        ∑ w : U, if s.val ∪ t.val ⊆ w.val then coeff f w.val else 0 from
          (Finset.sum_coe_sort U _).symm]
    suffices h : (∑ j : U, (inc U * Matrix.diagonal a) s j * inc U t j) =
        ∑ j : U, if s.val ∪ t.val ⊆ j.val then coeff f j.val else 0 by
      rw [← h]; ring
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_diagonal]
    by_cases hs : s.val ⊆ j.val <;> by_cases ht : t.val ⊆ j.val <;>
      simp [inc, a, Finset.union_subset_iff, hs, ht]
  have hentry (s t : U) : ∃ z : ℤ, B s t = r s * z := by
    rw [hB]
    have heq : (∑ w ∈ U, if s.val ∪ t.val ⊆ w then coeff f w else 0) =
        ∑ w ∈ support f, if s.val ∪ t.val ⊆ w then coeff f w else 0 :=
      Finset.sum_subset hsub fun w hw hn => by
        have hx : ¬ s.val ∪ t.val ⊆ w := fun h =>
          hn (hup s.val s.property w hw (Finset.subset_union_left.trans h))
        simp [hx]
    rw [heq]
    exact entry_factor f (htail n f) s.val t.val
  choose z hz using hentry
  let Z : Matrix (↥U) (↥U) ℤ := z
  have hmat : B = Matrix.diagonal r * Z.map (Int.castRingHom ℝ) := by
    ext s t
    rw [Matrix.diagonal_mul]
    exact hz s t
  have hleft : B.det = (2 : ℝ)^(2 * (∑ s ∈ U, s.card)) * ∏ s ∈ U, coeff f s := by
    have hd : (∏ s : U, d s) = (2 : ℝ)^((∑ s ∈ U, s.card)) := by
      change (∏ s : U, (2:ℝ)^s.val.card) = _
      rw [Finset.prod_coe_sort U (fun s => (2:ℝ)^s.card), Finset.prod_pow_eq_pow_sum]
    simp only [B, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose, inc_det,
      hd, one_mul, mul_one, two_mul, pow_add]
    rw [show (∏ s : U, a s) = ∏ s ∈ U, coeff f s from Finset.prod_coe_sort U (coeff f)]
    ring
  have hright : B.det = (2 : ℝ)^(U.erase ∅).card * (Z.det : ℝ) := by
    rw [hmat, Matrix.det_mul, Matrix.det_diagonal]
    rw [show (Z.map (Int.castRingHom ℝ)).det = (Z.det : ℝ) from ((Int.castRingHom ℝ).map_det Z).symm]
    exact congrArg (· * (Z.det : ℝ)) (row_prod U)
  refine ⟨Z.det, ?_, hleft.symm.trans hright⟩
  intro hzero
  have hcoeff : ∀ s ∈ U, coeff f s ≠ 0 := fun _ h => by simpa [support] using hsub h
  have hn : (2 : ℝ)^(2 * (∑ s ∈ U, s.card)) * ∏ s ∈ U, coeff f s ≠ 0 :=
    mul_ne_zero (by positivity) (Finset.prod_ne_zero_iff.mpr hcoeff)
  apply hn
  rw [← hleft, hright, hzero]
  simp

theorem signedProduct_of_upper (h : UpperProduct) : SignedProduct := by
  intro n f
  exact h n f (support f) (fun _ hs => hs) (fun _ _ _ hw _ => hw)

end Fei
