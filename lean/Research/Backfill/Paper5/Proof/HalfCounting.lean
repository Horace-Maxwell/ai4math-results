import Research.Backfill.Paper5.Proof.HalfFibreCounting

set_option autoImplicit false

namespace CodexPaper5.HalfCounting

open BackfillPaper5
open scoped Nat

abbrev FreeSets (n r : ℕ) := {F : Finset (Fin n) // F.card = r}

/-- Every half has exactly one free-set index; both dependent inverse laws are explicit. -/
def halfSigmaEquiv (D : Challenge.Fam) (n r : ℕ) :
    Challenge.Hr D n r ≃ Σ F : FreeSets n r, HalfFibreCounting.Fibre D n r F.val where
  toFun h := ⟨⟨h.val.1, h.property.1⟩, ⟨h.val, h.property, rfl⟩⟩
  invFun z := ⟨z.2.val, z.2.property.1⟩
  left_inv h := rfl
  right_inv z := by
    rcases z with ⟨⟨F, hF⟩, ⟨⟨G, m⟩, hl, hGF⟩⟩
    change G = F at hGF
    subst G
    rfl

theorem card_freeSets (n r : ℕ) : Fintype.card (FreeSets n r) = n.choose r := by
  simpa only [FreeSets, Fintype.card_fin] using (Fintype.card_finset_len (α := Fin n) r)

theorem ncard_Hr_eq_sum (D : Challenge.Fam) (n r : ℕ) :
    (Challenge.Hr D n r).ncard =
      ∑ F : FreeSets n r, Nat.card (HalfFibreCounting.Fibre D n r F.val) := by
  change Nat.card (Challenge.Hr D n r) = _
  exact (Nat.card_congr (halfSigmaEquiv D n r)).trans Nat.card_sigma

theorem ncard_Hr_B (n r : ℕ) (hle : r ≤ n) (hpar : r % 2 = n % 2) :
    (Challenge.Hr Challenge.Fam.B n r).ncard = n.choose r * (n - r - 1)‼ := by
  calc
    (Challenge.Hr Challenge.Fam.B n r).ncard =
        ∑ F : FreeSets n r, Nat.card (HalfFibreCounting.Fibre Challenge.Fam.B n r F.val) :=
      ncard_Hr_eq_sum Challenge.Fam.B n r
    _ = ∑ _F : FreeSets n r, (n - r - 1)‼ := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact HalfFibreCounting.card_fibre_B F.property hle hpar
    _ = n.choose r * (n - r - 1)‼ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_freeSets, Nat.cast_id]

theorem ncard_Hr_PB (n r : ℕ) (_hle : r ≤ n) :
    (Challenge.Hr Challenge.Fam.PB n r).ncard = n.choose r * Challenge.invCount (n - r) := by
  calc
    (Challenge.Hr Challenge.Fam.PB n r).ncard =
        ∑ F : FreeSets n r, Nat.card (HalfFibreCounting.Fibre Challenge.Fam.PB n r F.val) :=
      ncard_Hr_eq_sum Challenge.Fam.PB n r
    _ = ∑ _F : FreeSets n r, Challenge.invCount (n - r) := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact HalfFibreCounting.card_fibre_PB F.property
    _ = n.choose r * Challenge.invCount (n - r) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_freeSets, Nat.cast_id]

theorem check_CountH : Challenge.CountH := by
  constructor
  · exact ncard_Hr_B
  · exact ncard_Hr_PB

#print axioms CodexPaper5.HalfCounting.FreeSets
#print axioms CodexPaper5.HalfCounting.halfSigmaEquiv
#print axioms CodexPaper5.HalfCounting.card_freeSets
#print axioms CodexPaper5.HalfCounting.ncard_Hr_eq_sum
#print axioms CodexPaper5.HalfCounting.ncard_Hr_B
#print axioms CodexPaper5.HalfCounting.ncard_Hr_PB
#print axioms CodexPaper5.HalfCounting.check_CountH

end CodexPaper5.HalfCounting
