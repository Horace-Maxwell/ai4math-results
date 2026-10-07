import Research.Backfill.Paper5.Challenge

set_option autoImplicit false

namespace CodexPaper5

open BackfillPaper5 Function

/-- A preimage of zero under the first bijection must also be zero, by injectivity
of the product map. This uses both absorption identities and no finiteness. -/
theorem check_ZeroFixed : Challenge.ZeroFixed := by
  intro S op z hz α hα
  obtain ⟨w, hw⟩ := hα.1.2 z
  have hwz : w = z := hα.2.1 (by
    change op w (α w) = op z (α z)
    rw [hw, (hz w).2, (hz (α z)).1])
  exact hwz ▸ hw

/-- The explicit Rees map A is bijective: first recover its old last coordinate,
then the group coordinate, then the old first coordinate using a Latin column. -/
private theorem fA_bijective {r : ℕ} {H : Type*} (L : H → H → H)
    (phi : Challenge.Sym r → Challenge.Sym r)
    (hL : Challenge.IsLatin L) (hphi : Bijective phi) :
    Bijective (Challenge.fA L phi) := by
  constructor
  · rintro (_ | ⟨i, g, l⟩) (_ | ⟨j, h, m⟩) heq
    · rfl
    · simp [Challenge.fA] at heq
    · simp [Challenge.fA] at heq
    · simp only [Challenge.fA, Option.some.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨hl, hg, hi⟩
      cases hl
      have hgh : g = h := hphi.1 hg
      have hij : i = j := (hL.2 l).1 hi
      cases hgh
      cases hij
      rfl
  · rintro (_ | ⟨l, h, m⟩)
    · exact ⟨none, rfl⟩
    · obtain ⟨g, hg⟩ := hphi.2 h
      obtain ⟨i, hi⟩ := (hL.2 l).2 m
      refine ⟨some (i, g, l), ?_⟩
      simp only [Challenge.fA, hg, hi]

/-- On nonzero triples, multiplying by map A uses precisely the diagonal entry
of the original sandwich matrix. -/
private theorem product_fA_some {r : ℕ} {H : Type*}
    (P : H → H → Option (Challenge.Sym r)) (L : H → H → H)
    (phi : Challenge.Sym r → Challenge.Sym r)
    (hdiag : ∀ l, P l l = some 1) (i l : H) (g : Challenge.Sym r) :
    Challenge.rees0Mul P (some (i, g, l)) (Challenge.fA L phi (some (i, g, l))) =
      some (i, g * phi g, L i l) := by
  simp only [Challenge.fA, Challenge.rees0Mul, hdiag, Option.map_some, mul_one]

/-- The product map is bijective: recover the old first coordinate, then the
group coordinate from its complete mapping, then the last using a Latin row. -/
private theorem product_fA_bijective {r : ℕ} {H : Type*}
    (P : H → H → Option (Challenge.Sym r)) (L : H → H → H)
    (phi : Challenge.Sym r → Challenge.Sym r)
    (hdiag : ∀ l, P l l = some 1) (hL : Challenge.IsLatin L)
    (hprod : Bijective (fun g => g * phi g)) :
    Bijective (fun x => Challenge.rees0Mul P x (Challenge.fA L phi x)) := by
  constructor
  · rintro (_ | ⟨i, g, l⟩) (_ | ⟨j, h, m⟩) heq
    · rfl
    · simp [Challenge.fA, Challenge.rees0Mul, hdiag] at heq
    · simp [Challenge.fA, Challenge.rees0Mul, hdiag] at heq
    · simp only [product_fA_some P L phi hdiag, Option.some.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨hi, hg, hl⟩
      cases hi
      have hgh : g = h := hprod.1 hg
      have hlm : l = m := (hL.1 i).1 hl
      cases hgh
      cases hlm
      rfl
  · rintro (_ | ⟨i, h, m⟩)
    · exact ⟨none, rfl⟩
    · obtain ⟨g, hg⟩ := hprod.2 h
      obtain ⟨l, hl⟩ := (hL.1 i).2 m
      refine ⟨some (i, g, l), ?_⟩
      simpa only [hg, hl] using product_fA_some P L phi hdiag i l g

/-- Complete frozen Lemma 4.1, for the actual `fA` and actual Rees multiplication. -/
theorem check_Lemma41 : Challenge.Lemma41 := by
  intro r H _ _ P L phi hdiag hL hphi
  exact ⟨fA_bijective L phi hL hphi.1,
    product_fA_bijective P L phi hdiag hL hphi.2⟩

#print axioms check_ZeroFixed
#print axioms check_Lemma41

end CodexPaper5
