import Research.Backfill.Paper5.Proof.CMTransport

set_option autoImplicit false

namespace CodexPaper5.CMTransversal

open BackfillPaper5 Function

variable {G I : Type*} [Group G]

/-- Concrete two-sided transversal data. Both equivalences are required to be the actual
multiplication factorizations; no normality or complete-mapping conclusion is a field. -/
structure Data (K : Subgroup G) (I : Type*) where
  reps : I → G
  left : I × K ≃ G
  right : K × I ≃ G
  left_apply : ∀ (i : I) (p : K), left (i, p) = reps i * (p : G)
  right_apply : ∀ (p : K) (i : I), right (p, i) = (p : G) * reps i
  shift : Equiv.Perm I
  productIndex : Equiv.Perm I
  coeff : I → K
  rep_product : ∀ i, reps i * reps (shift i) = reps (productIndex i) * (coeff i : G)

variable {K : Subgroup G}

/-- Right-factor the product of a shifted representative with a subgroup element. -/
def rightPieces (D : Data K I) (i : I) (p : K) : K × I :=
  D.right.symm (D.reps (D.shift i) * (p : G))

def leftPart (D : Data K I) (i : I) (p : K) : K := (rightPieces D i p).1

def rightIndex (D : Data K I) (i : I) (p : K) : I := (rightPieces D i p).2

theorem cross_eq (D : Data K I) (i : I) (p : K) :
    D.reps (D.shift i) * (p : G) = (leftPart D i p : G) * D.reps (rightIndex D i p) := by
  calc
    D.reps (D.shift i) * (p : G) = D.right (rightPieces D i p) :=
      (D.right.apply_symm_apply _).symm
    _ = (leftPart D i p : G) * D.reps (rightIndex D i p) := D.right_apply _ _

theorem cross_cancel (D : Data K I) (i : I) (p : K) :
    (leftPart D i p : G)⁻¹ * D.reps (D.shift i) = D.reps (rightIndex D i p) * (p : G)⁻¹ := by
  calc
    (leftPart D i p : G)⁻¹ * D.reps (D.shift i) =
        (leftPart D i p : G)⁻¹ * (D.reps (D.shift i) * (p : G)) * (p : G)⁻¹ := by group
    _ = (leftPart D i p : G)⁻¹ *
        ((leftPart D i p : G) * D.reps (rightIndex D i p)) * (p : G)⁻¹ := by rw [cross_eq]
    _ = D.reps (rightIndex D i p) * (p : G)⁻¹ := by group

/-- Fixing the representative, the subgroup part of the right factorization is injective.
The proof uses uniqueness of the *left* factorization. -/
theorem leftPart_injective (D : Data K I) (i : I) : Injective (leftPart D i) := by
  intro p q hpq
  have he : D.left (rightIndex D i p, p⁻¹) = D.left (rightIndex D i q, q⁻¹) := by
    simp only [D.left_apply, Subgroup.coe_inv]
    calc
      D.reps (rightIndex D i p) * (p : G)⁻¹ =
          (leftPart D i p : G)⁻¹ * D.reps (D.shift i) := (cross_cancel D i p).symm
      _ = (leftPart D i q : G)⁻¹ * D.reps (D.shift i) := by rw [hpq]
      _ = D.reps (rightIndex D i q) * (q : G)⁻¹ := cross_cancel D i q
  exact inv_injective (congrArg Prod.snd (D.left.injective he))

/-- Fixing the subgroup element, the representative index is injective.
The proof uses uniqueness of the *right* factorization and the index permutation. -/
theorem rightIndex_injective (D : Data K I) (p : K) : Injective (fun i => rightIndex D i p) := by
  intro i j hij
  change rightIndex D i p = rightIndex D j p at hij
  have he : D.right ((leftPart D i p)⁻¹, D.shift i) =
      D.right ((leftPart D j p)⁻¹, D.shift j) := by
    simp only [D.right_apply, Subgroup.coe_inv]
    rw [cross_cancel D i p, cross_cancel D j p, hij]
  exact D.shift.injective (congrArg Prod.snd (D.right.injective he))

/-- Finite subgroup injectivity supplies an inverse, without a normal-subgroup hypothesis. -/
noncomputable def partEquiv [Finite G] (D : Data K I) (i : I) : K ≃ K :=
  Equiv.ofBijective (leftPart D i) (leftPart_injective D i).bijective_of_finite

/-- The actual complete-mapping candidate. Every input first has its unique left coordinates;
the subgroup coordinate is then inverted through `partEquiv`. -/
noncomputable def liftMap [Finite G] (D : Data K I) (φ : K → K) (x : G) : G :=
  let ip := D.left.symm x
  let p := (partEquiv D ip.1).symm ip.2
  D.left (rightIndex D ip.1 p, φ p)

/-- The formula on the coordinates used in the transversal proof. -/
theorem liftMap_apply [Finite G] (D : Data K I) (φ : K → K) (i : I) (p : K) :
    liftMap D φ (D.left (i, leftPart D i p)) = D.left (rightIndex D i p, φ p) := by
  have hp : (partEquiv D i).symm (leftPart D i p) = p :=
    (partEquiv D i).symm_apply_apply p
  simp only [liftMap, D.left.symm_apply_apply, hp]

/-- Every group element occurs in the coordinates of `liftMap_apply`. -/
theorem exists_input [Finite G] (D : Data K I) (x : G) :
    ∃ (i : I) (p : K), x = D.left (i, leftPart D i p) := by
  obtain ⟨⟨i, a⟩, hx⟩ := D.left.surjective x
  obtain ⟨p, hp⟩ := (partEquiv D i).surjective a
  refine ⟨i, p, ?_⟩
  change leftPart D i p = a at hp
  rw [hp]
  exact hx.symm

/-- The mapping is injective using the original mapping on the subgroup. -/
theorem liftMap_injective [Finite G] (D : Data K I) (φ : K → K) (hφ : Injective φ) :
    Injective (liftMap D φ) := by
  intro x y hxy
  obtain ⟨i, p, rfl⟩ := exists_input D x
  obtain ⟨j, q, rfl⟩ := exists_input D y
  rw [liftMap_apply, liftMap_apply] at hxy
  have hpq : p = q := hφ (congrArg Prod.snd (D.left.injective hxy))
  subst q
  have hij : i = j := rightIndex_injective D p (congrArg Prod.fst (D.left.injective hxy))
  subst j
  rfl

/-- The product formula in the ambient group. All coefficient terms are actual subgroup values. -/
theorem product_liftMap_apply [Finite G] (D : Data K I) (φ : K → K) (i : I) (p : K) :
    D.left (i, leftPart D i p) * liftMap D φ (D.left (i, leftPart D i p)) =
      D.left (D.productIndex i, D.coeff i * (p * φ p)) := by
  rw [liftMap_apply]
  simp only [D.left_apply, Subgroup.coe_mul]
  calc
    (D.reps i * (leftPart D i p : G)) * (D.reps (rightIndex D i p) * (φ p : G)) =
        D.reps i * ((leftPart D i p : G) * D.reps (rightIndex D i p)) * (φ p : G) := by group
    _ = D.reps i * (D.reps (D.shift i) * (p : G)) * (φ p : G) := by rw [← cross_eq D i p]
    _ = (D.reps i * D.reps (D.shift i)) * ((p : G) * (φ p : G)) := by group
    _ = (D.reps (D.productIndex i) * (D.coeff i : G)) * ((p : G) * (φ p : G)) := by
      rw [D.rep_product]
    _ = D.reps (D.productIndex i) * ((D.coeff i : G) * ((p : G) * (φ p : G))) := by group

/-- The product map is injective using the subgroup product map and the transversal product law. -/
theorem product_liftMap_injective [Finite G] (D : Data K I) (φ : K → K)
    (hφ : Injective (fun p : K => p * φ p)) : Injective (fun x : G => x * liftMap D φ x) := by
  intro x y hxy
  change x * liftMap D φ x = y * liftMap D φ y at hxy
  obtain ⟨i, p, rfl⟩ := exists_input D x
  obtain ⟨j, q, rfl⟩ := exists_input D y
  rw [product_liftMap_apply, product_liftMap_apply] at hxy
  have hij : i = j := D.productIndex.injective (congrArg Prod.fst (D.left.injective hxy))
  subst j
  have hpq : p = q := hφ (mul_left_cancel (congrArg Prod.snd (D.left.injective hxy)))
  subst q
  rfl

/-- The complete mapping is constructed and both bijections proved. Neither normality of K
nor a complete mapping of G is assumed. -/
theorem hasCM_of_data [Finite G] (D : Data K I) (hK : Challenge.HasCM K) : Challenge.HasCM G := by
  obtain ⟨φ, hφ⟩ := hK
  exact ⟨liftMap D φ, (liftMap_injective D φ hφ.1.1).bijective_of_finite,
    (product_liftMap_injective D φ hφ.2.1).bijective_of_finite⟩

#print axioms CodexPaper5.CMTransversal.cross_eq
#print axioms CodexPaper5.CMTransversal.leftPart_injective
#print axioms CodexPaper5.CMTransversal.rightIndex_injective
#print axioms CodexPaper5.CMTransversal.liftMap_injective
#print axioms CodexPaper5.CMTransversal.product_liftMap_apply
#print axioms CodexPaper5.CMTransversal.product_liftMap_injective
#print axioms CodexPaper5.CMTransversal.hasCM_of_data

end CodexPaper5.CMTransversal
