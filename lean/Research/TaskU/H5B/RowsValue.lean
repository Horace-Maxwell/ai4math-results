import Research.TaskU.H5B.SeedMarginals

namespace TaskU.H5.Spectrum
open Finset

theorem rows_value (s : Fin 5) (q : F → ℤ) (f : H → ℤ)
    (h : ∀ a b, marginal f a b = seed s b a + q a) :
    groupDet f = (5*seedA s+5*(∑a,q a)) *
      Cyc5.norm (Cyc5.add (baseRay s) (Cyc5.mul (Cyc5.scalar 5) (profile q))) *
      15625 * Cyc5.norm (TraceWords.nonlinear f)^5 := by
  have hm : marginal f = fun a b => wseed s a b + q a := funext (fun a => funext (h a))
  rw [integerFactorization, marginal_aug,hm,add_rows,(swapped_data s).1]
  simp_rw [marginal_ray,hm,ordinary_rows]
  rw [horizontal_rows,(swapped_data s).2.2]
  rfl

end TaskU.H5.Spectrum
