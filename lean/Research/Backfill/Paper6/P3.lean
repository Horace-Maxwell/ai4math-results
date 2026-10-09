import Research.Backfill.Paper6.MinDist
import Research.Backfill.Paper6.FlatBasics

/-!
# Paper 6 V3: the full minimum-weight structure theorem

For a minimum-weight word, any direction joining two support points must be
a period. Indeed, after a linear change of coordinates its two last-coordinate
slices have intersecting supports. A nonzero difference of those slices would
already have weight at least the whole word by MinDist and Lem22, contradicting
the positive intersection correction in the exact weight formula.

Invariance under every support-point difference makes the support an affine
subspace over the binary field. Its cardinality fixes its direction dimension.
The reverse implication is the actual polynomial indicator construction from
FlatBasics. Order zero and dimension zero are included explicitly.

Frozen FROZEN.json SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
Uncompiled source candidate; root controls validation and acceptance.
-/

set_option autoImplicit false

namespace Paper6MinimumStructure

open BackfillPaper6.V3

theorem binary_values : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide

abbrev lastVector (m : ℕ) : Pt (m + 1) := Pi.single (Fin.last m) 1

theorem lastVector_ne_zero (m : ℕ) : lastVector m ≠ 0 := by
  intro h
  have hbad : (1 : ZMod 2) = 0 := by
    simpa [lastVector] using congrFun h (Fin.last m)
  exact one_ne_zero hbad

/-- A nonzero prescribed direction can be made the last coordinate in every positive dimension. -/
theorem exists_direction_equiv (m : ℕ) (a : Pt (m + 1)) (ha : a ≠ 0) :
    ∃ φ : Pt (m + 1) ≃ₗ[ZMod 2] Pt (m + 1), φ (lastVector m) = a := by
  let e0 := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Pt (m + 1))
    (lastVector m) (lastVector_ne_zero m)
  let ea := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Pt (m + 1)) a ha
  obtain ⟨φ, hφ⟩ := Submodule.exists_linearEquiv_restrict_eq (e0.symm.trans ea)
  refine ⟨φ, ?_⟩
  have h : (ea 1 : Pt (m + 1)) = φ (e0 1) := by
    simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using hφ (e0 1)
  simpa [e0, ea] using h.symm

theorem snoc_add_last {m : ℕ} (x : Pt m) (t : ZMod 2) :
    Fin.snoc (α := fun _ => ZMod 2) x t + lastVector m =
      Fin.snoc (α := fun _ => ZMod 2) x (t + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Pi.add_apply, lastVector, Fin.snoc_last, Pi.single_eq_same]
  · simp only [Pi.add_apply, lastVector, Fin.snoc_castSucc,
      Pi.single_eq_of_ne (Fin.castSucc_ne_last j), add_zero]

theorem init_add_last {m : ℕ} (y : Pt (m + 1)) :
    Fin.init (y + lastVector m) = Fin.init y := by
  funext i
  change y i.castSucc + lastVector m i.castSucc = y i.castSucc
  simp only [lastVector, Pi.single_eq_of_ne (Fin.castSucc_ne_last i), add_zero]

/-- A supported pair in the last-coordinate direction supplies a common point of the slice supports. -/
theorem common_slice_support_of_pair {m : ℕ} (f : BFun (m + 1)) (y : Pt (m + 1))
    (hy : f y ≠ 0) (hshift : f (y + lastVector m) ≠ 0) :
    ∃ x : Pt m, half0 f x ≠ 0 ∧ half1 f x ≠ 0 := by
  rcases binary_values (y (Fin.last m)) with h0 | h1
  · have hy0 : Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 0 = y := by
      simpa only [h0] using Fin.snoc_init_self y
    have hnext : y + lastVector m =
        Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 1 := by
      calc
        y + lastVector m = Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 0 + lastVector m :=
          congrArg (fun z => z + lastVector m) hy0.symm
        _ = Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) (0 + 1) := snoc_add_last _ _
        _ = _ := by rw [zero_add]
    refine ⟨Fin.init y, ?_, ?_⟩
    · change f (Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 0) ≠ 0
      rw [hy0]
      exact hy
    · change f (Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 1) ≠ 0
      rw [← hnext]
      exact hshift
  · have hy1 : Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 1 = y := by
      simpa only [h1] using Fin.snoc_init_self y
    have hnext : y + lastVector m =
        Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 0 := by
      calc
        y + lastVector m = Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 1 + lastVector m :=
          congrArg (fun z => z + lastVector m) hy1.symm
        _ = Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) (1 + 1) := snoc_add_last _ _
        _ = _ := by rw [show (1 + 1 : ZMod 2) = 0 from by decide]
    refine ⟨Fin.init y, ?_, ?_⟩
    · change f (Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 0) ≠ 0
      rw [← hnext]
      exact hshift
    · change f (Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 1) ≠ 0
      rw [hy1]
      exact hy

/-- Minimality forces coincident slices whenever their supports intersect. -/
theorem delta_eq_zero_of_minimum_and_common_support (m r : ℕ) (hr : r ≤ m)
    (f : BFun (m + 1)) (hf : f ∈ RM (r + 1) (m + 1))
    (hw : hammingNorm f = 2 ^ (m - r))
    (hcommon : ∃ x : Pt m, half0 f x ≠ 0 ∧ half1 f x ≠ 0) :
    half0 f + half1 f = 0 := by
  by_contra hdelta
  have hmem := (Paper6HalfDecomposition.rm_slices_of_mem m r f hf).2
  have hlower := Paper6MinDistance.nonzero_weight_lower_bound m r hr
    (half0 f + half1 f) hmem hdelta
  have hinter : 0 < (Function.support (half0 f) ∩ Function.support (half1 f)).ncard := by
    apply (Set.ncard_pos (Set.toFinite _)).mpr
    obtain ⟨x, hx0, hx1⟩ := hcommon
    exact ⟨x, hx0, hx1⟩
  have hweight := (Paper6HalfDecomposition.weight_slices m f).trans
    (Paper6HalfDecomposition.weight_add_with_intersection (half0 f) (half1 f))
  rw [hw] at hweight
  omega

theorem invariant_last_of_delta_zero {m : ℕ} (f : BFun (m + 1))
    (hdelta : half0 f + half1 f = 0) (y : Pt (m + 1)) :
    f (y + lastVector m) = f y := by
  have hformula (z : Pt (m + 1)) : f z = half0 f (Fin.init z) := by
    have hz := Paper6HalfDecomposition.reconstruct m f z
    change f z = half0 f (Fin.init z) + z (Fin.last m) *
      ((half0 f + half1 f) (Fin.init z)) at hz
    rw [hdelta] at hz
    simpa only [Pi.zero_apply, mul_zero, add_zero] using hz
  calc
    f (y + lastVector m) = half0 f (Fin.init (y + lastVector m)) := hformula _
    _ = half0 f (Fin.init y) := congrArg (half0 f) (init_add_last y)
    _ = f y := (hformula y).symm

/-- Any direction joining two support points is a period of a minimum-weight word.
The zero direction, order zero, and dimension zero are all covered. -/
theorem translation_invariant_of_supported_pair (r m : ℕ) (hr : r ≤ m)
    (f : BFun m) (hf : f ∈ RM r m) (hw : hammingNorm f = 2 ^ (m - r))
    (a x : Pt m) (hx : f x ≠ 0) (hxa : f (x + a) ≠ 0) :
    ∀ y : Pt m, f (y + a) = f y := by
  by_cases ha : a = 0
  · intro y
    rw [ha, add_zero]
  · cases m with
    | zero =>
        exact (ha (funext fun i => Fin.elim0 i)).elim
    | succ m =>
        cases r with
        | zero =>
            rcases Paper6MinDistance.rm_zero_order_eq_zero_or_one (m + 1) f hf with rfl | rfl <;>
              intro y <;> rfl
        | succ r =>
            have hr' : r ≤ m := by omega
            obtain ⟨φ, hφ⟩ := exists_direction_equiv m a ha
            let F : BFun (m + 1) := fun y => f (φ y)
            have hF : F ∈ RM (r + 1) (m + 1) :=
              Paper6AffineInvariance.rm_precomposition φ.toAffineEquiv f hf
            have hwF : hammingNorm F = 2 ^ (m - r) := by
              calc
                hammingNorm F = hammingNorm f :=
                  Paper6AffineInvariance.weight_precomposition φ.toAffineEquiv f
                _ = 2 ^ (m + 1 - (r + 1)) := hw
                _ = 2 ^ (m - r) := by rw [show m + 1 - (r + 1) = m - r by omega]
            have hxF : F (φ.symm x) ≠ 0 := by
              simpa only [F, LinearEquiv.apply_symm_apply] using hx
            have hxaF : F (φ.symm x + lastVector m) ≠ 0 := by
              dsimp only [F]
              rw [map_add, LinearEquiv.apply_symm_apply, hφ]
              exact hxa
            have hcommon := common_slice_support_of_pair F (φ.symm x) hxF hxaF
            have hdelta := delta_eq_zero_of_minimum_and_common_support m r hr' F hF hwF hcommon
            intro y
            have hperiod := invariant_last_of_delta_zero F hdelta (φ.symm y)
            change f (φ (φ.symm y + lastVector m)) = f (φ (φ.symm y)) at hperiod
            simpa only [map_add, LinearEquiv.apply_symm_apply, hφ] using hperiod

/-- Translation invariance by support differences supplies the required affine closure. -/
theorem support_closed (r m : ℕ) (hr : r ≤ m)
    (f : BFun m) (hf : f ∈ RM r m) (hw : hammingNorm f = 2 ^ (m - r))
    (x y z : Pt m) (hx : x ∈ Function.support f) (hy : y ∈ Function.support f)
    (hz : z ∈ Function.support f) : x - y + z ∈ Function.support f := by
  have hpair : f (y + (x - y)) ≠ 0 := by
    rw [show y + (x - y) = x by abel]
    exact hx
  have hperiod := translation_invariant_of_supported_pair r m hr f hf hw
    (x - y) y hy hpair z
  change f (x - y + z) ≠ 0
  rw [show x - y + z = z + (x - y) by abel, hperiod]
  exact hz

/-- The carrier is the actual support, equipped with its proved affine-subspace closure. -/
noncomputable def supportFlat (r m : ℕ) (hr : r ≤ m)
    (f : BFun m) (hf : f ∈ RM r m) (hw : hammingNorm f = 2 ^ (m - r)) :
    AffineSubspace (ZMod 2) (Pt m) where
  carrier := Function.support f
  smul_vsub_vadd_mem' c := by
    intro x y z hx hy hz
    rcases binary_values c with h0 | h1
    · simpa only [h0, zero_smul, zero_vadd] using hz
    · simpa only [h1, one_smul, vsub_eq_sub, vadd_eq_add] using
        support_closed r m hr f hf hw x y z hx hy hz

theorem hammingNorm_ind {m : ℕ} (S : Set (Pt m)) : hammingNorm (ind S) = S.ncard := by
  classical
  unfold hammingNorm
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  by_cases hx : x ∈ S <;> simp [ind, hx]

theorem eq_ind_support {m : ℕ} (f : BFun m) : f = ind (Function.support f) := by
  classical
  funext x
  by_cases hx : x ∈ Function.support f
  · have hne : f x ≠ 0 := hx
    have hone : f x = 1 := (binary_values (f x)).resolve_left hne
    simp [ind, hx, hone]
  · have hzero : f x = 0 := by
      by_contra hne
      exact hx hne
    simp [ind, hx, hzero]

theorem support_ncard_eq_hammingNorm {m : ℕ} (f : BFun m) :
    (Function.support f).ncard = hammingNorm f := by
  rw [← hammingNorm_ind, ← eq_ind_support]

/-- The actual support is a nonempty flat of exactly the claimed dimension. -/
theorem minimum_word_is_flat (r m : ℕ) (hr : r ≤ m) (f : BFun m)
    (hf : f ∈ RM r m) (hw : hammingNorm f = 2 ^ (m - r)) :
    ∃ F : AffineSubspace (ZMod 2) (Pt m), IsFlat F (m - r) ∧ f = ind (F : Set (Pt m)) := by
  let F := supportFlat r m hr f hf hw
  have hcard : (F : Set (Pt m)).ncard = 2 ^ (m - r) :=
    (support_ncard_eq_hammingNorm f).trans hw
  have hnonempty : (F : Set (Pt m)).Nonempty := by
    apply (Set.ncard_pos (Set.toFinite _)).mp
    rw [hcard]
    exact Nat.two_pow_pos _
  obtain ⟨p, hp⟩ := hnonempty
  have hflatcard := Paper6FlatBasics.flat_ncard F p hp
    (Module.finrank (ZMod 2) F.direction) rfl
  have hdim : Module.finrank (ZMod 2) F.direction = m - r :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) (hflatcard.symm.trans hcard)
  refine ⟨F, ⟨⟨p, hp⟩, hdim⟩, ?_⟩
  exact eq_ind_support f

/-- FlatBasics supplies a genuine degree-at-most-r indicator polynomial, with the exact weight. -/
theorem flat_is_minimum_word (r m : ℕ) (hr : r ≤ m) (f : BFun m)
    (hflat : ∃ F : AffineSubspace (ZMod 2) (Pt m),
      IsFlat F (m - r) ∧ f = ind (F : Set (Pt m))) :
    f ∈ RM r m ∧ hammingNorm f = 2 ^ (m - r) := by
  obtain ⟨F, hF, rfl⟩ := hflat
  have hbasics := Paper6FlatBasics.check_FlatBasics m (m - r) F hF
  have horder : m - (m - r) = r := by omega
  constructor
  · rw [horder] at hbasics
    exact hbasics.2
  · exact (hammingNorm_ind (F : Set (Pt m))).trans hbasics.1

/-- Both implications of the complete frozen minimum-weight classification, for all r≤m. -/
theorem p3_minWeight : BackfillPaper6.V3.P3_minWeight := by
  intro r m hr f
  exact ⟨fun h => minimum_word_is_flat r m hr f h.1 h.2,
    flat_is_minimum_word r m hr f⟩

/-- Exact frozen contract check; this alias is not an additional mathematical result. -/
theorem check_P3_minWeight : BackfillPaper6.V3.P3_minWeight := p3_minWeight

end Paper6MinimumStructure

#print axioms Paper6MinimumStructure.binary_values
#print axioms Paper6MinimumStructure.lastVector
#print axioms Paper6MinimumStructure.lastVector_ne_zero
#print axioms Paper6MinimumStructure.exists_direction_equiv
#print axioms Paper6MinimumStructure.snoc_add_last
#print axioms Paper6MinimumStructure.init_add_last
#print axioms Paper6MinimumStructure.common_slice_support_of_pair
#print axioms Paper6MinimumStructure.delta_eq_zero_of_minimum_and_common_support
#print axioms Paper6MinimumStructure.invariant_last_of_delta_zero
#print axioms Paper6MinimumStructure.translation_invariant_of_supported_pair
#print axioms Paper6MinimumStructure.support_closed
#print axioms Paper6MinimumStructure.supportFlat
#print axioms Paper6MinimumStructure.hammingNorm_ind
#print axioms Paper6MinimumStructure.eq_ind_support
#print axioms Paper6MinimumStructure.support_ncard_eq_hammingNorm
#print axioms Paper6MinimumStructure.minimum_word_is_flat
#print axioms Paper6MinimumStructure.flat_is_minimum_word
#print axioms Paper6MinimumStructure.p3_minWeight
#print axioms Paper6MinimumStructure.check_P3_minWeight
#print Paper6MinimumStructure.check_P3_minWeight
