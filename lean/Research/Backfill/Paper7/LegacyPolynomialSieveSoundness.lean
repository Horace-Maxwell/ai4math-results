import Research.Backfill.Paper7.ModularPolynomialRejectSound
import Research.Backfill.Paper7.LegacyModuliAndWindows
import Research.Backfill.Paper7.SunSpectralWindowAndFactorization

/-!
# Paper 7: the full B/B2 and C/C2 polynomial rejection contract

Source-only candidate. No compilation or acceptance is claimed.
The actual integer factorizations come from the Sun spectral-window theorem;
the cleared polynomial is monic of degree 4*b by the cleared identity.
B/B2 retains the window [-9,9], while C/C2 retains its larger [-10,10]
window and the characteristic polynomial of the actual Sun graph.
Only integrality-to-total-multiplicity and strict-deficit rejection are proved.
No converse from passing a sieve to integrality is asserted.
-/

set_option autoImplicit false

namespace Paper7PolynomialSieve

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

/-- Enlarging the allowed window preserves the same concrete factor list. -/
theorem integerFactorizationOn_mono {f : Polynomial ℤ} {S T : Finset ℤ}
    (hST : S ⊆ T) (hf : IntegerFactorizationOn f S) :
    IntegerFactorizationOn f T := by
  obtain ⟨a, ha, hfa⟩ := hf
  exact ⟨a, fun z hz => hST (ha z hz), hfa⟩

#print axioms Paper7PolynomialSieve.integerFactorizationOn_mono

/-- C/C2 uses its original radius ten, without changing the proved roots. -/
theorem integerWindow_nine_subset_ten : integerWindow 9 ⊆ integerWindow 10 := by
  intro z hz
  have hz' : (-9 : ℤ) ≤ z ∧ z ≤ 9 := Finset.mem_Icc.mp hz
  change z ∈ Finset.Icc (-10 : ℤ) 10
  apply Finset.mem_Icc.mpr
  omega

#print axioms Paper7PolynomialSieve.integerWindow_nine_subset_ten

/-- The degree is the cardinality of the actual vertex type, including all arms. -/
theorem graphPhi_monic_degree (b : ℕ) (p q : Fin b → ℕ) :
    (graphPhi (SG b p q)).Monic ∧
      (graphPhi (SG b p q)).natDegree = nOf b p q := by
  classical
  constructor
  · exact Matrix.charpoly_monic _
  · unfold graphPhi
    rw [Matrix.charpoly_natDegree_eq_dim]
    exact Paper7Setup.sg_order b p q

#print axioms Paper7PolynomialSieve.graphPhi_monic_degree

/-- The complete forward multiplicity equality for every B/B2 modulus. -/
theorem integral_cleared_root_sum (b : ℕ) (p q : Fin b → ℕ)
    (hb : 3 ≤ b) (hn : nOf b p q ≤ 49) (ℓ : ℕ) (hℓ : ℓ ∈ bPrimes)
    (hG : IsIntegralGraph (SG b p q)) :
    modularRootSum ℓ (integerWindow 9) (clearedF b p q) = 4 * b := by
  classical
  have hparams := Paper7Moduli.check_LegacyModuliAndWindows.1 ℓ
    (Finset.mem_union_left _ (Finset.mem_union_left _ hℓ))
  have hlarge : 216 < ℓ := hparams.2
  have hinj := Paper7Moduli.integerWindow_injOn ℓ 9 (by omega)
  have hcleared := Paper7Cleared.check_ClearedCharacteristicPolynomial b p q hb
  have hfactor :=
    ((Paper7SpectralWindow.check_SunSpectralWindowAndFactorization b p q hb hn).2 hG).2
  have hreduce := check_ModularPolynomialRejectSound ℓ hparams.1
    (clearedF b p q) (integerWindow 9) hcleared.2.1 hinj
  exact (hreduce.2.2.2.1 hfactor).trans hcleared.2.2

#print axioms Paper7PolynomialSieve.integral_cleared_root_sum

/-- The complete forward equality for every C/C2 modulus and its radius ten. -/
theorem integral_graph_root_sum (b : ℕ) (p q : Fin b → ℕ)
    (hb : 3 ≤ b) (hn : nOf b p q ≤ 49) (ℓ : ℕ) (hℓ : ℓ ∈ cPrimes)
    (hG : IsIntegralGraph (SG b p q)) :
    modularRootSum ℓ (integerWindow 10) (graphPhi (SG b p q)) = nOf b p q := by
  classical
  have hparams := Paper7Moduli.check_LegacyModuliAndWindows.1 ℓ
    (Finset.mem_union_left _ (Finset.mem_union_right _ hℓ))
  have hlarge : 216 < ℓ := hparams.2
  have hinj := Paper7Moduli.integerWindow_injOn ℓ 10 (by omega)
  have hgraph := graphPhi_monic_degree b p q
  have hfactor9 :=
    ((Paper7SpectralWindow.check_SunSpectralWindowAndFactorization b p q hb hn).2 hG).1
  have hfactor10 := integerFactorizationOn_mono integerWindow_nine_subset_ten hfactor9
  have hreduce := check_ModularPolynomialRejectSound ℓ hparams.1
    (graphPhi (SG b p q)) (integerWindow 10) hgraph.1 hinj
  exact (hreduce.2.2.2.1 hfactor10).trans hgraph.2

#print axioms Paper7PolynomialSieve.integral_graph_root_sum

/-- Exactly the frozen four conclusions, with no extra hypothesis or converse. -/
theorem check_LegacyPolynomialSieveSoundness :
    BackfillPaper7.Challenge.Legacy.Algebra.LegacyPolynomialSieveSoundness := by
  intro b p q hb hn
  constructor
  · intro ℓ hℓ
    have hforward := integral_cleared_root_sum b p q hb hn ℓ hℓ
    refine ⟨hforward, ?_⟩
    intro hdeficit hG
    exact (ne_of_lt hdeficit) (hforward hG)
  · intro ℓ hℓ
    have hforward := integral_graph_root_sum b p q hb hn ℓ hℓ
    refine ⟨hforward, ?_⟩
    intro hdeficit hG
    exact (ne_of_lt hdeficit) (hforward hG)

#print axioms Paper7PolynomialSieve.check_LegacyPolynomialSieveSoundness

end Paper7PolynomialSieve
