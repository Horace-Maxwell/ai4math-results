import Research.TaskU.H5.Cyc5

namespace TaskU.H5.Cyc5

lemma val_scalar (n : ℤ) (z : ℂ) : val (scalar n) z = n := by simp [val,scalar]

lemma val_mul (v w : V) (z : ℂ) (hz : 1+z+z^2+z^3+z^4=0) :
    val (mul v w) z = val v z * val w z := by
  simp only [val,mul,Int.cast_sub,Int.cast_mul,Int.cast_add]
  linear_combination (-(v.b:ℂ)*(w.d:ℂ) - (v.c:ℂ)*(w.c:ℂ) + (v.c:ℂ)*(w.d:ℂ) - (v.d:ℂ)*(w.b:ℂ) + (v.d:ℂ)*(w.c:ℂ) - (v.d:ℂ)*(w.d:ℂ)*z^2 - z*((v.c:ℂ)*(w.d:ℂ) + (v.d:ℂ)*(w.c:ℂ) - (v.d:ℂ)*(w.d:ℂ))) * hz

lemma val_sigma2 (v : V) (z : ℂ) (hz : 1+z+z^2+z^3+z^4=0) :
    val (sigma2 v) z = val v (z^2) := by
  simp only [val,sigma2,Int.cast_neg,Int.cast_sub]
  linear_combination (-(v.c:ℂ) - (v.d:ℂ)*z^2 + (v.d:ℂ)*z) * hz

lemma val_sigma3 (v : V) (z : ℂ) (hz : 1+z+z^2+z^3+z^4=0) :
    val (sigma3 v) z = val v (z^3) := by
  simp only [val,sigma3,conj,sigma2,Int.cast_neg,Int.cast_sub]
  linear_combination (-(v.c:ℂ)*z^2 + (v.c:ℂ)*z - (v.d:ℂ)*z^5 + (v.d:ℂ)*z^4 - (v.d:ℂ)) * hz

lemma val_conj (v : V) (z : ℂ) (hz : 1+z+z^2+z^3+z^4=0) :
    val (conj v) z = val v (z^4) := by
  simp only [val,conj,Int.cast_neg,Int.cast_sub]
  linear_combination (-(v.b:ℂ) - (v.c:ℂ)*z^4 - (v.d:ℂ)*z^8 + (v.d:ℂ)*z^7 + (v.d:ℂ)*z^2 - z^3*(-(v.c:ℂ) + (v.d:ℂ))) * hz

lemma norm_embeddings (v : V) (z : ℂ) (hz : 1+z+z^2+z^3+z^4=0) :
    (norm v : ℂ) = val v z * val v (z^2) * val v (z^3) * val v (z^4) := by
  have h := congrArg (fun s => val s z) (norm_prod v)
  simp only [val_scalar,val_mul _ _ z hz,val_sigma2 _ z hz,val_sigma3 _ z hz,val_conj _ z hz] at h
  linear_combination -h

end TaskU.H5.Cyc5
