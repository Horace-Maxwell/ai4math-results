import Research.Backfill.Paper5.Proof.CyclePotential
import Research.Backfill.Paper5.Proof.ReesEven

set_option autoImplicit false

namespace CodexPaper5

open BackfillPaper5 Function
open scoped BigOperators

namespace ReesCycle

/-- The actual edge weight whose cycle sum is prescribed by the frozen condition. -/
def edgeWeight {r : ℕ} {H : Type} (P : H → H → Option (Challenge.Sym r))
    (ρ : Equiv.Perm H) (l : H) : ZMod 2 :=
  1 + Challenge.sOf P l (ρ l)

/-- The frozen cycle condition is precisely zero total weight around that cycle. -/
theorem edgeWeight_closed {r : ℕ} {H : Type}
    (P : H → H → Option (Challenge.Sym r)) (ρ : Equiv.Perm H)
    (hcycle : ∀ l, Challenge.CycleCond P ρ l) (b : H) :
    ∑ t ∈ Finset.range (minimalPeriod ρ b), edgeWeight P ρ ((ρ ^ t) b) = 0 := by
  simpa [edgeWeight, Challenge.CycleCond, Finset.sum_add_distrib,
    pow_succ', Equiv.Perm.mul_apply] using hcycle b

/-- Construct the actual coefficient function on every cycle, including the wrap-around edge. -/
theorem exists_coefficients {r : ℕ} {H : Type} [Finite H]
    (P : H → H → Option (Challenge.Sym r)) (ρ : Equiv.Perm H)
    (hcycle : ∀ l, Challenge.CycleCond P ρ l) :
    ∃ c : H → ZMod 2, ∀ l, c (ρ l) = c l + 1 + Challenge.sOf P l (ρ l) := by
  obtain ⟨c, hc⟩ := CyclePotential.exists_potential ρ (edgeWeight P ρ)
    (edgeWeight_closed P ρ hcycle)
  refine ⟨c, ?_⟩
  intro l
  simpa only [edgeWeight, add_assoc] using hc l

/-- A genuine nonzero sandwich entry has its actual parity in the quotient matrix. -/
theorem sign_edge {r : ℕ} {H : Type}
    (P : H → H → Option (Challenge.Sym r)) (ρ : Equiv.Perm H)
    (hρ : ∀ l, P l (ρ l) ≠ none) (l : H) :
    Challenge.sgnMat P l (ρ l) = some (Challenge.sOf P l (ρ l)) := by
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp (hρ l)
  simp [Challenge.sgnMat, Challenge.sOf, hp]

/-- The concrete frozen map C, with the concrete quotient multiplication, has both bijections. -/
theorem fC_complete {r : ℕ} {H : Type} [Finite H]
    (P : H → H → Option (Challenge.Sym r)) (hdiag : ∀ l, P l l = some 1)
    (ρ : Equiv.Perm H) (hρ : ∀ l, P l (ρ l) ≠ none)
    (L : H → H → H) (c : H → ZMod 2) (hL : Challenge.IsLatin L)
    (hc : ∀ l, c (ρ l) = c l + 1 + Challenge.sOf P l (ρ l)) :
    Challenge.IsCompleteMapping (Challenge.mulZ2 (Challenge.sgnMat P)) (Challenge.fC L ρ c) := by
  have hzero : ∀ l, Challenge.sgnMat P l l = some 0 := by
    intro l
    simp only [Challenge.sgnMat, hdiag, Option.map_some, CycleRemarks.sgn_one]
  change ReesCoreCompat.IsCompleteMapping (ReesCoreCompat.mul (Challenge.sgnMat P))
    (ReesCoreCompat.fC L ρ c)
  exact ReesCoreCompat.lemmaC (Challenge.sgnMat P) L ρ c
    (fun l => Challenge.sOf P l (ρ l)) hzero (sign_edge P ρ hρ) hc
    (fun i => (hL.1 i).1) (fun l => (hL.2 l).1)

end ReesCycle

/-- Complete frozen Lemma 4.4: the coefficient function exists, every prescribed map C works,
and a complete mapping of the actual symmetric-group Rees semigroup exists. -/
theorem check_Lemma44 : Challenge.Lemma44 := by
  intro r hr H _ _ P hdiag ρ hρ hcycle
  obtain ⟨c, hc⟩ := ReesCycle.exists_coefficients P ρ hcycle
  refine ⟨⟨c, hc⟩, ?_, ?_⟩
  · intro L c' hL hc'
    exact ReesCycle.fC_complete P hdiag ρ hρ L c' hL hc'
  · obtain ⟨L, hL⟩ := ReesEven.exists_latin H
    exact CodexPaper5.check_Lemma42 r hr H P hdiag
      ⟨Challenge.fC L ρ c, ReesCycle.fC_complete P hdiag ρ hρ L c hL hc⟩

#print axioms CodexPaper5.ReesCycle.edgeWeight_closed
#print axioms CodexPaper5.ReesCycle.exists_coefficients
#print axioms CodexPaper5.ReesCycle.sign_edge
#print axioms CodexPaper5.ReesCycle.fC_complete
#print axioms CodexPaper5.check_Lemma44

end CodexPaper5
