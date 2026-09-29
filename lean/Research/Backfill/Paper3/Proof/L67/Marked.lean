import Research.Backfill.Paper3.Proof.L67.W

/-!
# Vertex sets of `2 K_{d,d}` and the marked sums `W_{αβ}`

A vertex set of `2 K_{d,d}` is a quadruple `(L₀, R₀, L₁, R₁)` of subsets of `Fin d` (the sides of
the two copies), and it spans `|L₀||R₀| + |L₁||R₁|` edges (`quad`, `sum_quad`, `edgesIn_quad`).
Summing `f([a ∈ L], [b ∈ R]) z^{|L||R| - [a ∈ L][b ∈ R]}` over the vertex sets `L ⊔ R` of one
`K_{d,d}` gives `Σ_{α,β} f(α, β) W_{αβ}` (`sum_marked`): split each side at its marked vertex and
count the remaining vertices with binomial coefficients.
-/

set_option autoImplicit false

namespace P3L67

open Finset SimpleGraph Polynomial BackfillPaper3.Challenge P3Basic

section Quad

variable {d : ℕ}

/-- The vertex set of `2 K_{d,d}` with sides `L₀, R₀` in copy `0` and `L₁, R₁` in copy `1`. -/
def quad (L₀ R₀ L₁ R₁ : Finset (Fin d)) : Finset (Fin 2 × (Fin d ⊕ Fin d)) :=
  (fibresEquiv 2 (Fin d ⊕ Fin d)).symm ![L₀.disjSum R₀, L₁.disjSum R₁]

@[simp] theorem mem_quad_0_inl (L₀ R₀ L₁ R₁ : Finset (Fin d)) (x : Fin d) :
    ((0 : Fin 2), (Sum.inl x : Fin d ⊕ Fin d)) ∈ quad L₀ R₀ L₁ R₁ ↔ x ∈ L₀ := by
  simp [quad, fibresEquiv]

@[simp] theorem mem_quad_0_inr (L₀ R₀ L₁ R₁ : Finset (Fin d)) (y : Fin d) :
    ((0 : Fin 2), (Sum.inr y : Fin d ⊕ Fin d)) ∈ quad L₀ R₀ L₁ R₁ ↔ y ∈ R₀ := by
  simp [quad, fibresEquiv]

@[simp] theorem mem_quad_1_inl (L₀ R₀ L₁ R₁ : Finset (Fin d)) (x : Fin d) :
    ((1 : Fin 2), (Sum.inl x : Fin d ⊕ Fin d)) ∈ quad L₀ R₀ L₁ R₁ ↔ x ∈ L₁ := by
  simp [quad, fibresEquiv]

@[simp] theorem mem_quad_1_inr (L₀ R₀ L₁ R₁ : Finset (Fin d)) (y : Fin d) :
    ((1 : Fin 2), (Sum.inr y : Fin d ⊕ Fin d)) ∈ quad L₀ R₀ L₁ R₁ ↔ y ∈ R₁ := by
  simp [quad, fibresEquiv]

/-- A sum over the vertex sets of `V ⊕ W` is a double sum over pairs of vertex sets. -/
theorem sum_finset_sumType {M : Type*} [AddCommMonoid M] {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (F : Finset (α ⊕ β) → M) :
    ∑ B, F B = ∑ L : Finset α, ∑ R : Finset β, F (L.disjSum R) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (finsetSumEquiv α β) _ _
    (fun B => by simp [finsetSumEquiv, Finset.toLeft_disjSum_toRight])

/-- A sum over the vertex sets of `2 K_{d,d}` is a fourfold sum over the sides. -/
theorem sum_quad {M : Type*} [AddCommMonoid M] (φ : Finset (Fin 2 × (Fin d ⊕ Fin d)) → M) :
    ∑ A, φ A = ∑ L₀ : Finset (Fin d), ∑ R₀ : Finset (Fin d), ∑ L₁ : Finset (Fin d),
      ∑ R₁ : Finset (Fin d), φ (quad L₀ R₀ L₁ R₁) := by
  calc ∑ A, φ A = ∑ g : Fin 2 → Finset (Fin d ⊕ Fin d), φ ((fibresEquiv 2 _).symm g) :=
        Fintype.sum_equiv (fibresEquiv 2 _) _ _ (fun A => by rw [Equiv.symm_apply_apply])
    _ = ∑ p : Finset (Fin d ⊕ Fin d) × Finset (Fin d ⊕ Fin d),
          φ ((fibresEquiv 2 _).symm ![p.1, p.2]) :=
        Fintype.sum_equiv (finTwoArrowEquiv _) _ _ (fun g =>
          congrArg (fun g' => φ ((fibresEquiv 2 _).symm g'))
            ((finTwoArrowEquiv _).symm_apply_apply g).symm)
    _ = ∑ B₀, ∑ B₁, φ ((fibresEquiv 2 _).symm ![B₀, B₁]) := Fintype.sum_prod_type _
    _ = _ := by
      rw [sum_finset_sumType]
      refine Finset.sum_congr rfl fun L₀ _ => Finset.sum_congr rfl fun R₀ _ => ?_
      rw [sum_finset_sumType]
      rfl

/-- `e_{2K}(L₀ ⊔ R₀ ⊔ L₁ ⊔ R₁) = |L₀||R₀| + |L₁||R₁|`. -/
theorem edgesIn_quad (L₀ R₀ L₁ R₁ : Finset (Fin d)) :
    edgesIn (KddUnion 2 d) (quad L₀ R₀ L₁ R₁) = #L₀ * #R₀ + #L₁ * #R₁ := by
  rw [quad, edgesIn_copies, Fin.sum_univ_two]
  simp [edgesIn_Kdd]

end Quad

/-- Summing over the subsets of `Fin d` split at a marked element `a`. -/
theorem sum_finset_mark {M : Type*} [AddCommMonoid M] (d : ℕ) (hd : 1 ≤ d) (a : Fin d)
    (g : ℕ → ℕ → M) :
    ∑ L : Finset (Fin d), g #L (if a ∈ L then 1 else 0) =
      ∑ i ∈ range d, (d - 1).choose i • (g i 0 + g (i + 1) 1) := by
  have hs : (univ : Finset (Fin d)) = insert a (univ.erase a) :=
    (Finset.insert_erase (mem_univ a)).symm
  have ha : a ∉ univ.erase a := Finset.notMem_erase a univ
  have hc : #(univ.erase a) = d - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, Fintype.card_fin]
  rw [← Finset.powerset_univ, hs, Finset.sum_powerset_insert ha]
  have h1 : ∑ L ∈ (univ.erase a).powerset, g #L (if a ∈ L then 1 else 0) =
      ∑ L ∈ (univ.erase a).powerset, g #L 0 := by
    refine Finset.sum_congr rfl fun L hL => ?_
    have : a ∉ L := fun h => ha (Finset.mem_powerset.1 hL h)
    rw [ite_eq_right this]
  have h2 : ∑ L ∈ (univ.erase a).powerset, g #(insert a L) (if a ∈ insert a L then 1 else 0) =
      ∑ L ∈ (univ.erase a).powerset, g (#L + 1) 1 := by
    refine Finset.sum_congr rfl fun L hL => ?_
    have : a ∉ L := fun h => ha (Finset.mem_powerset.1 hL h)
    rw [ite_eq_left (Finset.mem_insert_self a L), Finset.card_insert_of_notMem this]
  have e1 : ∑ L ∈ (univ.erase a).powerset, g #L 0 =
      ∑ i ∈ range (#(univ.erase a) + 1), (#(univ.erase a)).choose i • g i 0 :=
    Finset.sum_powerset_apply_card (fun i => g i 0)
  have e2 : ∑ L ∈ (univ.erase a).powerset, g (#L + 1) 1 =
      ∑ i ∈ range (#(univ.erase a) + 1), (#(univ.erase a)).choose i • g (i + 1) 1 :=
    Finset.sum_powerset_apply_card (fun i => g (i + 1) 1)
  rw [h1, h2, e1, e2, hc, Nat.sub_add_cancel hd, ← Finset.sum_add_distrib]
  simp only [smul_add]

/-- `Σ_{α,β ∈ {0,1}} f(α, β) W_{αβ}`. -/
noncomputable def Wsum (d : ℕ) (f : ℕ → ℕ → ℤ[X]) : ℤ[X] :=
  f 0 0 * Wpoly d 0 0 + f 1 0 * Wpoly d 1 0 + f 0 1 * Wpoly d 0 1 + f 1 1 * Wpoly d 1 1

theorem pow_sub_one_mul (i j : ℕ) : (i + 1) * (j + 1) - 1 * 1 = i * j + 1 * j + 1 * i := by
  rw [show (i + 1) * (j + 1) = i * j + 1 * j + 1 * i + 1 * 1 by ring, Nat.add_sub_cancel]

/-- The marked sum over the vertex sets of one `K_{d,d}` with marked vertices `inl a`, `inr b`. -/
theorem sum_marked (d : ℕ) (hd : 1 ≤ d) (a b : Fin d) (f : ℕ → ℕ → ℤ[X]) :
    ∑ L : Finset (Fin d), ∑ R : Finset (Fin d),
        f (if a ∈ L then 1 else 0) (if b ∈ R then 1 else 0) *
          X ^ (#L * #R - (if a ∈ L then 1 else 0) * (if b ∈ R then 1 else 0)) =
      Wsum d f := by
  have inner : ∀ l α : ℕ, ∑ R : Finset (Fin d),
      f α (if b ∈ R then 1 else 0) * X ^ (l * #R - α * (if b ∈ R then 1 else 0)) =
        ∑ j ∈ range d, (d - 1).choose j •
          (f α 0 * X ^ (l * j - α * 0) + f α 1 * X ^ (l * (j + 1) - α * 1)) :=
    fun l α => sum_finset_mark d hd b (fun r β => f α β * X ^ (l * r - α * β))
  refine (sum_finset_mark d hd a (fun l α => ∑ R : Finset (Fin d),
      f α (if b ∈ R then 1 else 0) * X ^ (l * #R - α * (if b ∈ R then 1 else 0)))).trans ?_
  simp only [inner]
  unfold Wsum Wpoly
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pow_sub_one_mul]
  simp only [nsmul_eq_mul, map_mul, map_natCast, Nat.cast_mul, mul_zero, zero_mul, Nat.sub_zero,
    add_zero]
  ring

/-- The double marked sum over the vertex sets of `2 K_{d,d}`. -/
theorem sum_marked2 (d : ℕ) (hd : 1 ≤ d) (a₁ b₁ a₂ b₂ : Fin d) (F : ℕ → ℕ → ℕ → ℕ → ℤ[X]) :
    ∑ L₀ : Finset (Fin d), ∑ R₀ : Finset (Fin d), ∑ L₁ : Finset (Fin d), ∑ R₁ : Finset (Fin d),
        F (if a₁ ∈ L₀ then 1 else 0) (if b₁ ∈ R₀ then 1 else 0) (if a₂ ∈ L₁ then 1 else 0)
            (if b₂ ∈ R₁ then 1 else 0) *
          X ^ (#L₀ * #R₀ - (if a₁ ∈ L₀ then 1 else 0) * (if b₁ ∈ R₀ then 1 else 0)) *
          X ^ (#L₁ * #R₁ - (if a₂ ∈ L₁ then 1 else 0) * (if b₂ ∈ R₁ then 1 else 0)) =
      Wsum d (fun α β => Wsum d (F α β)) := by
  refine Eq.trans ?_ (sum_marked d hd a₁ b₁ (fun α β => Wsum d (F α β)))
  refine Finset.sum_congr rfl fun L₀ _ => Finset.sum_congr rfl fun R₀ _ => ?_
  rw [← sum_marked d hd a₂ b₂ (F _ _), Finset.sum_mul]
  refine Finset.sum_congr rfl fun L₁ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun R₁ _ => ?_
  ring

end P3L67
