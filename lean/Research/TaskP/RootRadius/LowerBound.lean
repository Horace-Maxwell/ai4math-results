import Research.TaskP.RootRadius.RootDisk
import Research.TaskP.RootRadius.JoinPolynomial

open Set Metric Filter Polynomial
open scoped Topology
namespace TaskP.GraphRootRadius.Proof
open Challenge

theorem recover_root {a c s m : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s) (hm : 1 < m)
    {ω v : ℂ} (hω : ω ≠ 0) (hv : v ∈ Complex.slitPlane) (E : ℂ[X])
    (hQ : 1+delta c s E (warg a c s m ω v) ∈ Complex.slitPlane)
    (hW : 1-(warg a c s m ω v)^a ∈ Complex.slitPlane) (he : residual a c s E ω m v = 0) :
    (1+delta c s E (warg a c s m ω v))^m = 1-((scale a c s m : ℂ)*ω*v)^a := by
  let Q := 1+delta c s E (warg a c s m ω v)
  let W := 1-(warg a c s m ω v)^a
  let S := scale a c s m
  have hL : (Real.log m : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos (by exact_mod_cast hm)).ne'
  have hS : 0 < S := scale_pos ha hc hs hm
  have hSc : (S:ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hv0 := Complex.slitPlane_ne_zero hv
  have eq : (m:ℂ)*Complex.log Q = a*(Real.log S : ℂ)+a*Complex.log v+
      Complex.log (-ω^a)+Complex.log W := by
    change (m:ℂ)/_ * Complex.log Q - (a:ℂ)*(Real.log S / Real.log m : ℝ) -
      ((a:ℂ)*Complex.log v+Complex.log (-ω^a)+Complex.log W)/_ = 0 at he
    simp only [Complex.ofReal_div] at he
    field_simp [hL] at he
    linear_combination he
  apply_fun Complex.exp at eq
  have hE : Complex.exp (Real.log S : ℂ) = (S : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hS]
  have hQ0 : Q ≠ 0 := Complex.slitPlane_ne_zero hQ
  have hW0 : W ≠ 0 := Complex.slitPlane_ne_zero hW
  simp only [Complex.exp_add, Complex.exp_nat_mul, Complex.exp_log hQ0,
    Complex.exp_log hW0, Complex.exp_log hv0,
    Complex.exp_log (neg_ne_zero.mpr (pow_ne_zero a hω)), hE] at eq
  change Q^m = 1 - ((S:ℂ)*ω*v)^a
  rw [eq]
  dsimp only [W, warg]
  change (S:ℂ)^a*v^a * -ω^a * (1-((ω*v)⁻¹ / (S:ℂ))^a) = _
  simp only [div_pow, inv_pow, mul_pow]
  field_simp
  ring

theorem normalized_eq_one_delta {V : Type*} [Fintype V] (B : SimpleGraph V) :
    ∃ E : ℂ[X], ∀ w : ℂ, (normalized B).eval w =
      1+delta (minimumSize B) (minimumCount B) E w := by
  obtain ⟨E,h⟩ := normalized_tail B
  refine ⟨E,fun w => ?_⟩
  rw [h]
  simp [delta, pow_succ]
  ring

theorem lower_bound {V : Type*} [Fintype V] [Nonempty V] (B : SimpleGraph V)
    {a : ℕ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, (1-ε)*scale a (minimumSize B) (minimumCount B) m ≤
      rootRadius (petalJoin a m B) := by
  let c := minimumSize B
  let s := minimumCount B
  have hc : 0 < c := by classical exact Nat.succ_pos _
  have hs : 0 < s := minimumCount_pos B
  obtain ⟨E,hE⟩ := normalized_eq_one_delta B
  obtain ⟨ω,hω⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) hc
  have hω0 : ω ≠ 0 := by rintro rfl; simp [zero_pow hc.ne'] at hω
  have hωnorm : ‖ω‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg ω) hc.ne').mp (by
    simp [← norm_pow, hω])
  have hη : 0 < ε/2 := by positivity
  have hR := (scale_atTop ha hc hs).eventually_ge_atTop (1/(ε/2))
  filter_upwards [residual_zeros ha hc hs hω E hη, hR, eventually_gt_atTop 1] with
    m ⟨v,hv,hsl,hQ,hW,he⟩ hwide hm
  let S := scale a c s m
  let y := (S:ℂ)*ω*v
  have hS : 0 < S := scale_pos ha hc hs hm
  have hy : y ≠ 0 := mul_ne_zero (mul_ne_zero (by exact_mod_cast hS.ne') hω0)
    (Complex.slitPlane_ne_zero hsl)
  have hw : y⁻¹ = warg a c s m ω v := by dsimp [y, S, warg]; ring
  have hroot : (dominationPolynomial (petalJoin a m B)).eval (y-1) = 0 := by
    apply (root_equation (by omega) B hy).mpr
    rw [hE,hw]
    exact recover_root ha hc hs hm hω0 hsl E hQ hW he
  let : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
  have ham := attain_graph (petalJoin a m B)
  apply le_trans _ (ham.2 (show ‖y-1‖ ∈ _ from ⟨y-1,hroot,rfl⟩))
  have hvn := norm_sub_norm_le (1:ℂ) v
  rw [← dist_eq_norm, dist_comm] at hvn
  have hyn := norm_sub_norm_le y (1:ℂ)
  have hmod : ‖y‖ = S * ‖v‖ := by simp [y, Complex.norm_real, abs_of_pos hS, hωnorm]
  rw [hmod,norm_one] at hyn
  rw [norm_one] at hvn
  have h1 : 1 ≤ S*(ε/2) := (div_le_iff₀ hη).mp hwide
  change (1-ε)*S ≤ _
  nlinarith [mul_lt_mul_of_pos_left (lt_of_le_of_lt hvn hv) hS]

end TaskP.GraphRootRadius.Proof
