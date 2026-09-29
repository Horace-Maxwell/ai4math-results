import Research.Backfill.Paper3.Proof.Basic

/-!
# Paper 3 back-fill: the edge polynomial (`PolyFacts`)

`P_{G ⊕ F} = P_G P_F`, `P_{K_{d,d}} = P_d`, `P_{mG} = P_G^m`, and `N_{≤t}(G) = Σ_{s ≤ t} [z^s] P_G`,
from the edge-count decompositions of `Research.Backfill.Paper3.Proof.Basic` and the bijections
`Finset (V ⊕ W) ≃ Finset V × Finset W`, `Finset (Fin m × W) ≃ (Fin m → Finset W)`.
-/

set_option autoImplicit false

namespace P3Basic

open Finset SimpleGraph Polynomial BackfillPaper3.Challenge

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem edgePoly_sum (G : SimpleGraph V) (F : SimpleGraph W) [DecidableRel G.Adj]
    [DecidableRel F.Adj] : edgePoly (G ⊕g F) = edgePoly G * edgePoly F := by
  unfold edgePoly
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (finsetSumEquiv V W) _ _ (fun A => ?_)
  rw [← pow_add, ← edgesIn_sum]
  simp [finsetSumEquiv, Finset.toLeft_disjSum_toRight]

theorem edgePoly_copies (m : ℕ) (G : SimpleGraph W) [DecidableRel G.Adj] :
    edgePoly (copies m G) = edgePoly G ^ m := by
  unfold edgePoly
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Fintype.sum_equiv (fibresEquiv m W) _ _ (fun A => ?_)
  rw [Finset.prod_pow_eq_pow_sum, ← edgesIn_copies, Equiv.symm_apply_apply]

/-- `Σ_{S ⊆ [d]} f(|S|) = Σ_a C(d, a) f(a)`. -/
theorem sum_finset_fin_apply_card (d : ℕ) (f : ℕ → ℤ[X]) :
    ∑ S : Finset (Fin d), f #S = ∑ a ∈ range (d + 1), d.choose a • f a := by
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card, Finset.card_univ, Fintype.card_fin]

theorem edgePoly_Kdd (d : ℕ) : edgePoly (Kdd d) = Pd d := by
  have h1 : edgePoly (Kdd d) =
      ∑ S : Finset (Fin d), ∑ T : Finset (Fin d), (X : ℤ[X]) ^ (#S * #T) := by
    unfold edgePoly
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (finsetSumEquiv (Fin d) (Fin d)) _ _ (fun A => ?_)
    have := edgesIn_Kdd d A.toLeft A.toRight
    rw [Finset.toLeft_disjSum_toRight] at this
    simp [finsetSumEquiv, this]
  have h2 : ∀ j : ℕ, ∑ T : Finset (Fin d), (X : ℤ[X]) ^ (j * #T) =
      ∑ b ∈ range (d + 1), d.choose b • (X : ℤ[X]) ^ (j * b) :=
    fun j => sum_finset_fin_apply_card d (fun k => X ^ (j * k))
  rw [h1]
  simp only [h2]
  rw [sum_finset_fin_apply_card d (fun a => ∑ b ∈ range (d + 1), d.choose b • (X : ℤ[X]) ^ (a * b))]
  unfold Pd
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [nsmul_eq_mul, ← map_natCast Polynomial.C]

/-- `N_{≤t}(G) = Σ_{s ≤ t} [z^s] P_G`. -/
theorem iCount_eq_sum_coeff (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) :
    (iCount G t : ℤ) = ∑ s ∈ range (t + 1), (edgePoly G).coeff s := by
  simp only [edgePoly, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]
  rw [iCount, Finset.card_filter]
  push_cast
  rfl

theorem check_PolyFacts : PolyFacts :=
  ⟨fun _ _ _ _ _ _ G F _ _ => edgePoly_sum G F, edgePoly_Kdd,
    fun m d => (edgePoly_copies m (Kdd d)).trans (by rw [edgePoly_Kdd]),
    fun _ _ _ G _ t => iCount_eq_sum_coeff G t⟩

#print axioms check_PolyFacts

end P3Basic
