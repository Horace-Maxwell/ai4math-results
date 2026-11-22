import Research.TaskP.RootRadius.Scale

open Filter Polynomial
open scoped Topology
namespace TaskP.GraphRootRadius.Proof
open Challenge

noncomputable def delta (c s : ℕ) (E : ℂ[X]) (w : ℂ) : ℂ :=
  w^c * (-(s : ℂ) + w * E.eval w)

noncomputable def warg (a c s m : ℕ) (ω v : ℂ) : ℂ :=
  ((ω*v)⁻¹) / (scale a c s m : ℂ)

noncomputable def residual (a c s : ℕ) (E : ℂ[X]) (ω : ℂ) (m : ℕ) (v : ℂ) : ℂ :=
  let w := warg a c s m ω v
  let L := (Real.log m : ℂ)
  (m : ℂ)/L * Complex.log (1+delta c s E w) -
    (a : ℂ)*(Real.log (scale a c s m) / Real.log m : ℝ) -
    ((a : ℂ)*Complex.log v + Complex.log (-ω^a) + Complex.log (1-w^a))/L

noncomputable def logSlope := dslope (fun x : ℂ => Complex.log (1+x)) 0

theorem logSlope_tendsto : Tendsto logSlope (𝓝 0) (𝓝 1) := by
  have hd : HasDerivAt (fun x : ℂ => Complex.log (1+x)) 1 0 := by
    convert! ((hasDerivAt_id (0 : ℂ)).const_add 1).clog (by simp) using 1
    norm_num
  have h := (continuousAt_dslope_same.mpr hd.differentiableAt).tendsto
  simpa [logSlope, hd.deriv] using h

theorem log_id (x : ℂ) : x * logSlope x = Complex.log (1+x) := by
  simpa [logSlope] using sub_smul_dslope (fun z : ℂ => Complex.log (1+z)) 0 x

theorem warg_limit {ι : Type*} {l : Filter ι} {M : ι → ℕ} {v : ι → ℂ} {p ω : ℂ}
    {a c s : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s) (hω : ω ≠ 0)
    (hp : p ≠ 0) (hm : Tendsto M l atTop) (hv : Tendsto v l (𝓝 p)) :
    Tendsto (fun i => warg a c s (M i) ω (v i)) l (𝓝 0) := by
  have hS := ((scale_atTop ha hc hs).comp hm).inv_tendsto_atTop
  have hSc : Tendsto (fun i => ((scale a c s (M i) : ℂ))⁻¹) l (𝓝 0) := by
    simpa using hS.ofReal
  simpa [warg, div_eq_mul_inv] using ((hv.const_mul ω).inv₀ (mul_ne_zero hω hp)).mul hSc

theorem delta_limit {ι : Type*} {l : Filter ι} {w : ι → ℂ} {c s : ℕ} (hc : 0 < c)
    (E : ℂ[X]) (hw : Tendsto w l (𝓝 0)) :
    Tendsto (fun i => delta c s E (w i)) l (𝓝 0) := by
  have hEval := E.continuous.continuousAt.tendsto.comp hw
  simpa [delta, zero_pow hc.ne'] using
    (hw.pow c).mul ((hw.mul hEval).const_add (-(s : ℂ)))

theorem scaled_log {a c s m : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s) (hm : 1 < m)
    (E : ℂ[X]) (ω v : ℂ) :
    let w := warg a c s m ω v
    (m : ℂ)/(Real.log m : ℂ) * Complex.log (1 + delta c s E w) =
      (a : ℂ) / ((c : ℂ)*s) * ((ω*v)⁻¹)^c *
      (-(s:ℂ) + w*E.eval w) * logSlope (delta c s E w) := by
  dsimp only
  let S : ℂ := scale a c s m
  have hL : (Real.log m : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos (by exact_mod_cast hm)).ne'
  have hM : (m:ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hA : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hC : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hS : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hpow : S^c = (c:ℂ)*s*m/(a*(Real.log m : ℂ)) := by
    dsimp [S]
    exact_mod_cast scale_pow ha hc hs hm
  rw [← log_id (delta c s E _)]
  generalize logSlope (delta c s E (warg a c s m ω v)) = q
  unfold delta
  change _ * ((((ω*v)⁻¹ / S)^c * _) * q) = _
  rw [div_pow, hpow]
  field_simp

theorem residual_limit {ι : Type*} {l : Filter ι} {M : ι → ℕ} {v : ι → ℂ} {p ω : ℂ}
    {a c s : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s) (hω : ω^c = -1)
    (hp : p ∈ Complex.slitPlane) (E : ℂ[X])
    (hm : Tendsto M l atTop) (hv : Tendsto v l (𝓝 p)) :
    Tendsto (fun i => residual a c s E ω (M i) (v i)) l
      (𝓝 (((a : ℂ)/c)*(p⁻¹^c-1))) := by
  have hω0 : ω ≠ 0 := by rintro rfl; simp [zero_pow hc.ne'] at hω
  let w := fun i => warg a c s (M i) ω (v i)
  have hw : Tendsto w l (𝓝 0) := warg_limit ha hc hs hω0 (Complex.slitPlane_ne_zero hp) hm hv
  have hδ := delta_limit (s := s) hc E hw
  have hE := E.continuous.continuousAt.tendsto.comp hw
  have hfirst := (((((hv.const_mul ω).inv₀ (mul_ne_zero hω0 (Complex.slitPlane_ne_zero hp))).pow c
    ).const_mul ((a:ℂ)/((c:ℂ)*s))).mul ((hw.mul hE).const_add (-(s:ℂ)))).mul
      (logSlope_tendsto.comp hδ)
  have hsecond := ((scale_log_limit ha hc hs).ofReal.comp hm).const_mul (a : ℂ)
  have hL : Tendsto (fun i => (Real.log (M i) : ℂ)⁻¹) l (𝓝 0) := by
    simpa using ((logNat_atTop.comp hm).inv_tendsto_atTop).ofReal
  have hOne : Tendsto (fun i => 1-(w i)^a) l (𝓝 (1 : ℂ)) := by
    simpa [zero_pow ha.ne'] using (hw.pow a).const_sub 1
  have hthird := ((((hv.clog hp).const_mul (a : ℂ)).add_const (Complex.log (-ω^a))).add
    (hOne.clog Complex.one_mem_slitPlane)).mul hL
  have h := (hfirst.sub hsecond).sub hthird
  have hC : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hS : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  convert! h.congr' (f₂ := fun i => residual a c s E ω (M i) (v i)) ?_ using 1
  · simp [mul_inv_rev, mul_pow, inv_pow, hω]
    field_simp
  · filter_upwards [hm.eventually (eventually_gt_atTop 1)] with i hi
    dsimp only [residual]
    rw [scaled_log ha hc hs hi]
    simp [w, div_eq_mul_inv]

end TaskP.GraphRootRadius.Proof
