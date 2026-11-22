import Research.TaskP.PrimeMedialRacks.Enumeration

namespace TaskP.PrimeMedialRacks
open Challenge

/-- Affine coordinates for a rack invariant under all translations, when its left
    translation at zero normalizes the translation group. -/
theorem normalized_coordinates {p : ℕ} [Fact p.Prime] (op : Operation (ZMod p))
    (hr : IsRack op) (hn : ¬ TwoReductive op)
    (shift : ∀ t x y, op (t+x) (t+y) = t + op x y)
    (norm : ∀ t, ∃ w, ∀ y, op 0 (t+y) = w + op 0 y) :
    ∃ k : Parameter p, ∀ x y, op x y = affine k.1 x y := by
  let c := op 0 0
  let f : ZMod p →+ ZMod p := {
    toFun := fun t => op 0 t - c
    map_zero' := sub_self _
    map_add' := by
      intro t y
      obtain ⟨w, hw⟩ := norm t
      have ht : op 0 t = w+c := by simpa [c] using hw 0
      rw [hw,ht]
      abel }
  let k := f 1
  have hf (t : ZMod p) : f t = t*k := by
    conv_lhs => rw [← t.intCast_zmod_cast, ← zsmul_one (t.cast : ℤ), map_zsmul]
    rw [zsmul_eq_mul, t.intCast_zmod_cast]
  have h0 (t : ZMod p) : op 0 t = t*k+c := by
    have h := hf t
    change op 0 t - c = t*k at h
    linear_combination h
  have form (x y : ZMod p) : op x y = (1-k)*x+k*y+c := by
    have h := shift x 0 (y-x)
    rw [add_zero, show x+(y-x)=y by abel, h0] at h
    rw [h]
    ring
  have hk1 : k ≠ 1 := by
    intro h
    apply hn
    intro x y u v
    simp only [form (op x u) v,form (op y u) v,h,sub_self,zero_mul]
  have hk0 : k ≠ 0 := by
    intro h
    have he : op 0 0 = op 0 1 := by simp [h0,h]
    exact zero_ne_one ((hr.1 0).1 he)
  have hc : c = 0 := by
    have h := hr.2 0 0 0
    change op 0 c = op c c at h
    rw [h0,form] at h
    apply (mul_eq_zero.mp (show (1-k)*c=0 by linear_combination -h)).resolve_left
    exact sub_ne_zero.mpr hk1.symm
  refine ⟨⟨k,hk0,hk1⟩,fun x y => ?_⟩
  simpa [hc,affine] using form x y

end TaskP.PrimeMedialRacks
