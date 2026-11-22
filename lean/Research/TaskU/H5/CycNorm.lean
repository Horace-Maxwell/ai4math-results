import Research.TaskU.H5.Cyc5
import Mathlib.Algebra.Field.ZMod

namespace TaskU.H5.Cyc5

lemma normForm_cast {q : ℕ} (v : V) :
    (norm v : ZMod q) = normForm (v.a : ZMod q) (v.b : ZMod q) (v.c : ZMod q) (v.d : ZMod q) := by
  simp [norm,normForm]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private lemma inert_test : ∀ q ∈ ([2,3,7] : List ℕ),
    ∀ a b c d : ZMod q, normForm a b c d = 0 → a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  intro q h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide +kernel

lemma inert_fourth (v : V) (q : ℕ) (hq : q ∈ ([2,3,7] : List ℕ)) (h : (q : ℤ) ∣ norm v) :
    (q : ℤ)^4 ∣ norm v := by
  have hx : (norm v : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr h
  rw [normForm_cast] at hx
  obtain ⟨ha,hb,hc,hd⟩ := inert_test q hq _ _ _ _ hx
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hb hc hd
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  obtain ⟨c,hc⟩ := hc
  obtain ⟨d,hd⟩ := hd
  refine ⟨normForm a b c d, ?_⟩
  simp only [norm,ha,hb,hc,hd,normForm]
  ring

set_option maxRecDepth 16000 in
set_option maxHeartbeats 800000 in
private lemma residue5 : ∀ a b c d : ZMod 5,
    normForm a b c d = (a+b+c+d)^4 := by decide +kernel

lemma norm_mod_five (v : V) : (norm v : ZMod 5) = (sumCoeff v : ZMod 5)^4 := by
  rw [normForm_cast, residue5]
  push_cast [sumCoeff]
  rfl

lemma five_dvd_norm_iff (v : V) : (5:ℤ) ∣ norm v ↔ 5 ∣ sumCoeff v := by
  change ((5:ℕ):ℤ) ∣ norm v ↔ ((5:ℕ):ℤ) ∣ sumCoeff v
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, norm_mod_five]
  exact (by decide : ∀ x : ZMod 5, x^4=0 ↔ x=0) _

end TaskU.H5.Cyc5
