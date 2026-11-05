import Research.Backfill.Paper7.LegacyTransfer

/-! Exact cast/scaling for the frozen reverse-ordered transfer product. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CRTAlgebra
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem ordinary_cast_square_lower (m : ℤ) (hm : 2 ≤ m.natAbs) :
    (4 : ℝ) ≤ (m : ℝ) ^ 2 := by
  have hi := (Int.natAbs_le_iff_sq_le (a := (2 : ℤ)) (b := m)).mp (by simpa using hm)
  norm_num at hi
  exact_mod_cast hi
#print axioms Paper7CRTAlgebra.ordinary_cast_square_lower

theorem ordinary_cast_ne (m : ℤ) (hm : 2 ≤ m.natAbs) :
    (m : ℝ) ≠ -1 ∧ (m : ℝ) ≠ 0 ∧ (m : ℝ) ≠ 1 ∧ (m : ℝ) ^ 2 - 1 ≠ 0 := by
  have hs := ordinary_cast_square_lower m hm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> nlinarith
#print axioms Paper7CRTAlgebra.ordinary_cast_ne

theorem transferH_cast_ne_zero (m : ℤ) (hm : 2 ≤ m.natAbs) :
    (transferH m : ℝ) ≠ 0 := by
  have h := ordinary_cast_ne m hm
  simp only [transferH, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_one]
  exact mul_ne_zero h.2.1 h.2.2.2
#print axioms Paper7CRTAlgebra.transferH_cast_ne_zero

theorem integerTk_cast (b : ℕ) (x : PQ b) (m : ℤ) (hm : 2 ≤ m.natAbs)
    (k : Fin b) :
    (integerTk x m k).map (fun z => (z : ℝ)) =
      (transferH m : ℝ) • Tk b x.1 x.2 (m : ℝ) k := by
  have hm0 := (ordinary_cast_ne m hm).2.1
  have hden := (ordinary_cast_ne m hm).2.2.2
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · change (transferS x m k : ℝ) =
      (transferH m : ℝ) * ((m : ℝ) - fk b x.1 x.2 (m : ℝ) k)
    simp only [transferS, transferH, fk, Int.cast_sub, Int.cast_mul,
      Int.cast_pow, Int.cast_one, Int.cast_natCast]
    field_simp [hm0, hden]
    ring
  · change ((-transferH m : ℤ) : ℝ) = (transferH m : ℝ) * (-1)
    simp
  · change (transferH m : ℝ) = (transferH m : ℝ) * 1
    simp
  · change ((0 : ℤ) : ℝ) = (transferH m : ℝ) * 0
    simp
#print axioms Paper7CRTAlgebra.integerTk_cast

/-- Proved for the exact list order, with no commutation or reversal of factors. -/
theorem integer_product_cast (b : ℕ) (x : PQ b) (m : ℤ) (hm : 2 ≤ m.natAbs)
    (l : List (Fin b)) :
    ((l.map (integerTk x m)).prod).map (fun z => (z : ℝ)) =
      (transferH m : ℝ) ^ l.length • (l.map (Tk b x.1 x.2 (m : ℝ))).prod := by
  let φ : Matrix (Fin 2) (Fin 2) ℤ →+* Matrix (Fin 2) (Fin 2) ℝ :=
    (Int.castRingHom ℝ).mapMatrix
  have hk (k : Fin b) : φ (integerTk x m k) =
      (transferH m : ℝ) • Tk b x.1 x.2 (m : ℝ) k := integerTk_cast b x m hm k
  change φ ((l.map (integerTk x m)).prod) = _
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, hk, ih,
      List.length_cons, pow_succ']
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
#print axioms Paper7CRTAlgebra.integer_product_cast

theorem integerMono_scaling (b : ℕ) (x : PQ b) (m : ℤ) (hm : 2 ≤ m.natAbs) :
    (integerMono x m).map (fun z => (z : ℝ)) =
      ((transferH m : ℝ) ^ b) • Mono b x.1 x.2 (m : ℝ) := by
  simpa only [integerMono, Mono, List.length_reverse, List.length_finRange] using
    integer_product_cast b x m hm (List.finRange b).reverse
#print axioms Paper7CRTAlgebra.integerMono_scaling

theorem integerMono_trace_cast (b : ℕ) (x : PQ b) (m : ℤ) (hm : 2 ≤ m.natAbs) :
    ((integerMono x m).trace : ℝ) =
      (transferH m : ℝ) ^ b * (Mono b x.1 x.2 (m : ℝ)).trace := by
  calc
    ((integerMono x m).trace : ℝ) =
        ((integerMono x m).map (fun z => (z : ℝ))).trace := by
          simp only [Matrix.trace_fin_two, Matrix.map_apply, Int.cast_add]
    _ = (((transferH m : ℝ) ^ b) • Mono b x.1 x.2 (m : ℝ)).trace :=
      congrArg Matrix.trace (integerMono_scaling b x m hm)
    _ = _ := Matrix.trace_smul _ _
#print axioms Paper7CRTAlgebra.integerMono_trace_cast

theorem integerMono_trace_eq_iff (b : ℕ) (x : PQ b) (m : ℤ) (hm : 2 ≤ m.natAbs) :
    (integerMono x m).trace = 2 * (transferH m) ^ b ↔
      (Mono b x.1 x.2 (m : ℝ)).trace = 2 := by
  have hp : (transferH m : ℝ) ^ b ≠ 0 := pow_ne_zero _ (transferH_cast_ne_zero m hm)
  have ht := integerMono_trace_cast b x m hm
  constructor
  · intro h
    have hc : ((integerMono x m).trace : ℝ) = 2 * (transferH m : ℝ) ^ b := by
      exact_mod_cast h
    apply mul_left_cancel₀ hp
    linarith
  · intro h
    have hc : ((integerMono x m).trace : ℝ) = 2 * (transferH m : ℝ) ^ b := by
      rw [ht, h]
      ring
    exact_mod_cast hc
#print axioms Paper7CRTAlgebra.integerMono_trace_eq_iff

theorem integer_matrix_cast_injective :
    Function.Injective (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (fun z => (z : ℝ))) := by
  intro A B h
  apply Matrix.ext
  intro i j
  have hij := congrFun (congrFun h i) j
  change (A i j : ℝ) = (B i j : ℝ) at hij
  exact_mod_cast hij
#print axioms Paper7CRTAlgebra.integer_matrix_cast_injective

theorem scalar_identity_cast (t : ℤ) :
    (t • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (fun z => (z : ℝ)) =
      (t : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j <;> simp [hij]
#print axioms Paper7CRTAlgebra.scalar_identity_cast

theorem integerMono_scalar_eq_iff (b : ℕ) (x : PQ b) (m : ℤ) (hm : 2 ≤ m.natAbs) :
    integerMono x m = (transferH m) ^ b • (1 : Matrix (Fin 2) (Fin 2) ℤ) ↔
      Mono b x.1 x.2 (m : ℝ) = 1 := by
  have hp : (transferH m : ℝ) ^ b ≠ 0 := pow_ne_zero _ (transferH_cast_ne_zero m hm)
  constructor
  · intro h
    have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (fun z => (z : ℝ))) h
    rw [integerMono_scaling b x m hm, scalar_identity_cast, Int.cast_pow] at hc
    apply Matrix.ext
    intro i j
    have hij := congrFun (congrFun hc i) j
    change (transferH m : ℝ) ^ b * (Mono b x.1 x.2 (m : ℝ)) i j =
      (transferH m : ℝ) ^ b * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j at hij
    exact mul_left_cancel₀ hp hij
  · intro h
    apply integer_matrix_cast_injective
    change (integerMono x m).map (fun z => (z : ℝ)) =
      ((transferH m) ^ b • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (fun z => (z : ℝ))
    rw [integerMono_scaling b x m hm, h, scalar_identity_cast, Int.cast_pow]
#print axioms Paper7CRTAlgebra.integerMono_scalar_eq_iff

end Paper7CRTAlgebra
