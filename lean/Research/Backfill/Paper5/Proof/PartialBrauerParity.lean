import Research.Backfill.Paper5.Proof.HalfCounting

set_option autoImplicit false

namespace CodexPaper5.PartialBrauerParity

open BackfillPaper5

/-- Inversion pairs all non-self-inverse elements of an even-cardinality finite group. -/
theorem even_self_inverse_of_even_card (G : Type*) [Group G] [Fintype G]
    (heven : Even (Fintype.card G)) : Even (Nat.card {x : G // x * x = 1}) := by
  classical
  let q : Equiv.Perm G := Equiv.inv G
  have hq : q ^ 2 = 1 := by
    rw [pow_two]
    apply Equiv.ext
    intro x
    change (x⁻¹)⁻¹ = x
    exact inv_inv x
  have hs : q.support = Finset.univ.filter (fun x : G => ¬ (x * x = 1)) := by
    apply Finset.ext
    intro x
    rw [Equiv.Perm.mem_support, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    change x⁻¹ ≠ x ↔ ¬ (x * x = 1)
    exact not_congr inv_eq_iff_mul_eq_one
  have hscard : q.support.card =
      Fintype.card G - Fintype.card {x : G // x * x = 1} := by
    calc
      q.support.card = (Finset.univ.filter (fun x : G => ¬ (x * x = 1))).card :=
        congrArg Finset.card hs
      _ = Fintype.card {x : G // ¬ (x * x = 1)} :=
        (Fintype.card_subtype (fun x : G => ¬ (x * x = 1))).symm
      _ = Fintype.card G - Fintype.card {x : G // x * x = 1} :=
        Fintype.card_subtype_compl (fun x : G => x * x = 1)
  have hdvd : 2 ∣ Fintype.card G - Fintype.card {x : G // x * x = 1} := by
    simpa only [hscard] using Equiv.Perm.two_dvd_card_support hq
  have hdiff := Nat.mod_eq_zero_of_dvd hdvd
  have htotal := Nat.even_iff.mp heven
  have hle := Fintype.card_subtype_le (fun x : G => x * x = 1)
  have hfixed : Even (Fintype.card {x : G // x * x = 1}) := by
    rw [Nat.even_iff]
    omega
  simpa only [Nat.card_eq_fintype_card] using hfixed

/-- The frozen permutation-subtype count is even at every size at least two. -/
theorem even_invCount (k : ℕ) (hk : 2 ≤ k) : Even (Challenge.invCount k) := by
  have hcard : Even (Fintype.card (Equiv.Perm (Fin k))) := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact even_iff_two_dvd.mpr (Nat.dvd_factorial (by decide : 0 < 2) hk)
  exact even_self_inverse_of_even_card (Equiv.Perm (Fin k)) hcard

/-- The only difference-one case allowed by the frozen hypotheses is (n,r)=(4,3). -/
theorem even_choose_mul_invCount (n r : ℕ) (hn : 4 ≤ n) (hr : r = 2 ∨ r = 3)
    (hlt : r < n) : Even (n.choose r * Challenge.invCount (n - r)) := by
  by_cases hd : 2 ≤ n - r
  · exact (even_invCount (n - r) hd).mul_left (n.choose r)
  · have hex : n = 4 ∧ r = 3 := by
      rcases hr with hr | hr <;> omega
    rcases hex with ⟨rfl, rfl⟩
    have hfour : Even ((4 : ℕ).choose 3) := ⟨2, by decide⟩
    exact hfour.mul_right (Challenge.invCount (4 - 3))

theorem even_ncard_Hr_PB (n r : ℕ) (hn : 4 ≤ n) (hr : r = 2 ∨ r = 3)
    (hlt : r < n) : Even (Challenge.Hr Challenge.Fam.PB n r).ncard := by
  rw [HalfCounting.ncard_Hr_PB n r (Nat.le_of_lt hlt)]
  exact even_choose_mul_invCount n r hn hr hlt

theorem check_Lemma61 : Challenge.Lemma61 := by
  refine ⟨even_invCount, ?_⟩
  intro n r hn hr hlt
  exact ⟨even_choose_mul_invCount n r hn hr hlt, even_ncard_Hr_PB n r hn hr hlt⟩

#print axioms CodexPaper5.PartialBrauerParity.even_self_inverse_of_even_card
#print axioms CodexPaper5.PartialBrauerParity.even_invCount
#print axioms CodexPaper5.PartialBrauerParity.even_choose_mul_invCount
#print axioms CodexPaper5.PartialBrauerParity.even_ncard_Hr_PB
#print axioms CodexPaper5.PartialBrauerParity.check_Lemma61

end CodexPaper5.PartialBrauerParity
