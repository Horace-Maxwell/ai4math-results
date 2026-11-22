import Research.TaskP.GeomSimplex.UCoordinates

namespace TaskP.GeomSimplex.Proof

open TaskP.GeomSimplex.Challenge

private def Witness (t k : ℕ) : Prop :=
  ∃ a b : Fin k → Lattice 3, (∀ i, a i ≠ b i) ∧ ∀ e : Fin k → Bool,
    ∀ j, -budget (t : ℤ) j ≤ uform (∑ i, if e i then b i else a i) j

private theorem pack_of_witness {t k : ℕ} (ht : 0 < t) (h : Witness t k) :
    packs (dilate t (simplex verticesU)) k := by
  obtain ⟨a, b, hn, hc⟩ := h
  have hcP : Convex ℝ (dilate t (simplex verticesU)) := by
    have he : dilate t (simplex verticesU) = {p | ∀ j, -budget (t : ℝ) j ≤ uform p j} :=
      Set.ext fun _ => dilateU_facets t ht _
    rw [he]
    exact convex_facets _
  exact pack_of_endpoints hcP a b hn (fun e => (dilateU_int _ ht _).2 (hc e))

private theorem witness_add {s t k l : ℕ} (hs : Witness s k) (ht : Witness t l) :
    Witness (s + t) (k + l) := by
  obtain ⟨a, b, hn, hc⟩ := hs
  obtain ⟨a', b', hn', hc'⟩ := ht
  refine ⟨Fin.addCases a a', Fin.addCases b b', ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hn, hn']
  · intro e j
    rw [Fin.sum_univ_add, form_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    have h₁ := hc (fun i => e (Fin.castAdd l i)) j
    have h₂ := hc' (fun i => e (Fin.natAdd k i)) j
    have hsum := add_le_add h₁ h₂
    convert hsum using 1
    simp only [budget, Nat.cast_add]
    split <;> ring

/-- A segment from p to p + k•v gives k integral factors. Only the two extreme
values of each linear form enter the feasibility check. -/
private theorem line_witness {k t : ℕ} (hk : 0 < k) (p v : Lattice 3) (hv : v ≠ 0)
    (ha : ∀ j, -budget (t : ℤ) j ≤ uform p j)
    (hb : ∀ j, -budget (t : ℤ) j ≤ uform p j + k * uform v j) : Witness t k := by
  let i₀ : Fin k := ⟨0, hk⟩
  let a (i : Fin k) : Lattice 3 := if i = i₀ then p else 0
  refine ⟨a, fun i => a i + v, fun i h => hv (by simpa using h.symm), ?_⟩
  intro e j
  have he (i : Fin k) :
      uform (if e i then a i + v else a i) j =
        uform (a i) j + (if e i then uform v j else 0) := by
    cases e i <;> simp [form_add]
  have zeroform : uform (0 : Lattice 3) j = 0 := by fin_cases j <;> decide
  have hasum : (∑ i, uform (a i) j) = uform p j := by
    have ha' (i : Fin k) : uform (a i) j = if i = i₀ then uform p j else 0 := by
      by_cases h : i = i₀ <;> simp [a, h, zeroform]
    simp [ha']
  rw [form_sum]
  simp only [he, Finset.sum_add_distrib, hasum]
  by_cases pos : 0 ≤ uform v j
  · have hn : 0 ≤ ∑ i, if e i then uform v j else 0 :=
      Finset.sum_nonneg fun i _ => by split <;> omega
    linarith [ha j]
  · have hn : ∑ _i : Fin k, uform v j ≤ ∑ i, if e i then uform v j else 0 :=
      Finset.sum_le_sum fun i _ => by split <;> omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hn
    linarith [hb j]

private theorem six : Witness 2 6 := by
  apply line_witness (by decide) (![1, 0, 1]) (![2, 3, 0])
  · decide
  all_goals decide

private theorem nine : Witness 3 9 := by
  apply line_witness (by decide) (![0, 0, 2]) (![3, 4, 0])
  · decide
  all_goals decide

private theorem witness_all (n : ℕ) : Witness (n + 2) (3 * (n + 2)) := by
  induction n using Nat.twoStepInduction with
  | zero => exact six
  | one => exact nine
  | more n hn _ =>
    convert witness_add hn six using 1

theorem lowerU {t : ℕ} (ht : 2 ≤ t) : packs (dilate t (simplex verticesU)) (3 * t) := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t-2, by omega⟩
  exact pack_of_witness (by omega) (witness_all n)

end TaskP.GeomSimplex.Proof
