import Research.Backfill.Paper7.ConnectedPerron

/-! Explicit two-color signs and actual adjacency eigenvector transport.
These declarations are source-only candidates until Root's real validation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroProjectors
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7Admissible

def signTwist {V : Type} (eps w : V → ℝ) : V → ℝ := by
  exact fun i => eps i * w i
#print axioms Paper7IntroProjectors.signTwist

theorem signTwist_involutive {V : Type} (eps w : V → ℝ)
    (hs : ∀ i, eps i = 1 ∨ eps i = -1) : signTwist eps (signTwist eps w) = w := by
  funext i
  rcases hs i with hi | hi <;> simp [signTwist, hi]
#print axioms Paper7IntroProjectors.signTwist_involutive

theorem signTwist_norm {V : Type} [Fintype V] (eps w : V → ℝ)
    (hs : ∀ i, eps i = 1 ∨ eps i = -1) :
    signTwist eps w ⬝ᵥ signTwist eps w = w ⬝ᵥ w := by
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _hi
  rcases hs i with hi | hi <;> simp [signTwist, hi]
#print axioms Paper7IntroProjectors.signTwist_norm

theorem adjacency_signTwist {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (eps w : V → ℝ)
    (hflip : ∀ i j, G.Adj i j → eps i = -eps j) :
    G.adjMatrix ℝ *ᵥ signTwist eps w = -signTwist eps (G.adjMatrix ℝ *ᵥ w) := by
  funext i
  change (∑ j, G.adjMatrix ℝ i j * (eps j * w j)) =
    -(eps i * ∑ j, G.adjMatrix ℝ i j * w j)
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hij : G.Adj i j
  · have he : eps j = -eps i := by linarith [hflip i j hij]
    simp only [SimpleGraph.adjMatrix_apply, ite_eq_left hij, one_mul, he]
    ring
  · simp only [SimpleGraph.adjMatrix_apply, ite_eq_right hij, zero_mul, mul_zero, neg_zero]
#print axioms Paper7IntroProjectors.adjacency_signTwist

theorem signTwist_eigenvector {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (eps w : V → ℝ) (r : ℝ)
    (hflip : ∀ i j, G.Adj i j → eps i = -eps j)
    (hw : G.adjMatrix ℝ *ᵥ w = r • w) :
    G.adjMatrix ℝ *ᵥ signTwist eps w = (-r) • signTwist eps w := by
  rw [adjacency_signTwist G eps w hflip, hw]
  funext i
  simp only [signTwist, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring
#print axioms Paper7IntroProjectors.signTwist_eigenvector

theorem colorable_two_has_real_sign {V : Type} (G : SimpleGraph V)
    (hB : G.Colorable 2) :
    ∃ eps : V → ℝ, (∀ i, eps i = 1 ∨ eps i = -1) ∧
      ∀ i j, G.Adj i j → eps i = -eps j := by
  obtain ⟨c⟩ := hB
  let eps : V → ℝ := fun i => if c i = 0 then 1 else -1
  refine ⟨eps, ?_, ?_⟩
  · intro i
    by_cases hi : c i = 0
    · exact Or.inl (ite_eq_left hi)
    · exact Or.inr (ite_eq_right hi)
  · intro i j hij
    have hc := c.valid hij
    have hi : c i = 0 ∨ c i = 1 := by omega
    have hj : c j = 0 ∨ c j = 1 := by omega
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact (hc (hi.trans hj.symm)).elim
    · simp [eps, hi, hj]
    · simp [eps, hi, hj]
    · exact (hc (hi.trans hj.symm)).elim
#print axioms Paper7IntroProjectors.colorable_two_has_real_sign

theorem negative_three_eigenvector_proportional
    {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (eps f w : V → ℝ) (hs : ∀ i, eps i = 1 ∨ eps i = -1)
    (hflip : ∀ i j, G.Adj i j → eps i = -eps j)
    (hf : ∀ i, 0 < f i) (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (hAw : G.adjMatrix ℝ *ᵥ w = (-3 : ℝ) • w) :
    ∃ t : ℝ, w = t • signTwist eps f := by
  have he : G.adjMatrix ℝ *ᵥ signTwist eps w = (3 : ℝ) • signTwist eps w := by
    simpa only [neg_neg] using signTwist_eigenvector G eps w (-3) hflip hAw
  obtain ⟨t, ht⟩ := graph_perron_proportional G hG 3 f hf hAf (signTwist eps w) he
  refine ⟨t, ?_⟩
  have hh := congrArg (signTwist eps) ht
  rw [signTwist_involutive eps w hs] at hh
  rw [hh]
  funext i
  simp only [signTwist, Pi.smul_apply, smul_eq_mul]
  ring
#print axioms Paper7IntroProjectors.negative_three_eigenvector_proportional

theorem positive_three_bipartite_signed_norm_zero
    {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (eps f : V → ℝ)
    (hflip : ∀ i j, G.Adj i j → eps i = -eps j)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f) :
    f ⬝ᵥ signTwist eps f = 0 := by
  have hg := signTwist_eigenvector G eps f 3 hflip hAf
  have hc := G.isSymm_adjMatrix.dotProduct_mulVec_comm (x := f) (y := signTwist eps f)
  rw [hAf, hg, dotProduct_smul, dotProduct_smul] at hc
  rw [dotProduct_comm (signTwist eps f) f] at hc
  simp only [smul_eq_mul] at hc
  linarith
#print axioms Paper7IntroProjectors.positive_three_bipartite_signed_norm_zero

theorem positive_three_bipartite_half_norm
    {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (eps f : V → ℝ)
    (hs : ∀ i, eps i = 1 ∨ eps i = -1)
    (hflip : ∀ i j, G.Adj i j → eps i = -eps j)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f) :
    (∑ i, if eps i = 1 then f i ^ 2 else 0) = (f ⬝ᵥ f) / 2 ∧
    (∑ i, if eps i = -1 then f i ^ 2 else 0) = (f ⬝ᵥ f) / 2 := by
  have hz := positive_three_bipartite_signed_norm_zero G eps f hflip hAf
  have hp (i : V) :
      2 * (if eps i = 1 then f i ^ 2 else 0) = f i * f i + f i * (eps i * f i) := by
    by_cases hi : eps i = 1
    · rw [ite_eq_left hi, hi]
      ring
    · have hm : eps i = -1 := (hs i).resolve_left hi
      rw [ite_eq_right hi, hm]
      ring
  have hn (i : V) :
      2 * (if eps i = -1 then f i ^ 2 else 0) = f i * f i - f i * (eps i * f i) := by
    by_cases hi : eps i = -1
    · rw [ite_eq_left hi, hi]
      ring
    · have hm : eps i = 1 := (hs i).resolve_right hi
      rw [ite_eq_right hi, hm]
      ring
  have hps : (∑ i, 2 * (if eps i = 1 then f i ^ 2 else 0)) =
      ∑ i, (f i * f i + f i * (eps i * f i)) :=
    Finset.sum_congr rfl (fun i _hi => hp i)
  have hns : (∑ i, 2 * (if eps i = -1 then f i ^ 2 else 0)) =
      ∑ i, (f i * f i - f i * (eps i * f i)) :=
    Finset.sum_congr rfl (fun i _hi => hn i)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hps
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hns
  change 2 * (∑ i, if eps i = 1 then f i ^ 2 else 0) = f ⬝ᵥ f + f ⬝ᵥ signTwist eps f at hps
  change 2 * (∑ i, if eps i = -1 then f i ^ 2 else 0) = f ⬝ᵥ f - f ⬝ᵥ signTwist eps f at hns
  rw [hz] at hps hns
  constructor <;> linarith
#print axioms Paper7IntroProjectors.positive_three_bipartite_half_norm

end Paper7IntroProjectors
