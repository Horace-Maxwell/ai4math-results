import Research.TaskP.GradedWilf.Challenge
namespace TaskP.GradedWilf
open Challenge

abbrev frob (a b : ℕ) := a*b-a-b

theorem bound_add {a b : ℕ} (ha : 2 ≤ a) (hb : a < b) : a+b < a*b := by
  nlinarith [Nat.mul_le_mul_right b ha]

theorem scalar_iff {a b x : ℕ} : x ∈ scalar a b ↔ ∃ u v : ℕ, u*a+v*b=x := by
  simpa only [scalar, smul_eq_mul] using AddSubmonoid.mem_closure_pair a b x

theorem frob_spec {a b : ℕ} (ha : 2 ≤ a) (hb : a < b) (hc : a.Coprime b) :
    frob a b ∉ scalar a b ∧ ∀ k > frob a b, k ∈ scalar a b :=
  frobeniusNumber_iff.mp (frobeniusNumber_pair hc (by omega) (by omega))

theorem one_gap {a b : ℕ} (ha : 2 ≤ a) (hb : a < b) : 1 ∉ scalar a b := by
  rintro h
  obtain ⟨u,v,he⟩ := scalar_iff.mp h
  by_cases hu : u = 0
  · subst u
    simp only [Nat.zero_mul, Nat.zero_add] at he
    have hv : 0 < v := by by_contra! h; simp [show v = 0 by omega] at he
    have := Nat.mul_le_mul_right b hv
    omega
  · have := Nat.mul_le_mul_right a (show 1 ≤ u by omega)
    omega

theorem reflect_mem {a b t : ℕ} (ha : 2 ≤ a) (hb : a < b) (hc : a.Coprime b)
    (ht : t ≤ frob a b) : frob a b - t ∈ scalar a b ↔ t ∉ scalar a b := by
  obtain ⟨hgap,habove⟩ := frob_spec ha hb hc
  constructor
  · intro hf h
    exact hgap (by simpa [Nat.sub_add_cancel ht] using (scalar a b).add_mem hf h)
  · intro ht'
    have hab := bound_add ha hb
    have hrepr := habove (t + a*b) (by dsimp [frob]; omega)
    obtain ⟨u,v,huv⟩ := scalar_iff.mp hrepr
    have hu : u < b := by
      by_contra! hh
      apply ht'
      refine scalar_iff.mpr ⟨u-b,v,?_⟩
      have h := Nat.sub_add_cancel hh
      have he := congrArg (· * a) h
      simp only [Nat.add_mul] at he
      nlinarith only [he,huv]
    have hv : v < a := by
      by_contra! hh
      apply ht'
      refine scalar_iff.mpr ⟨u,v-a,?_⟩
      have he := congrArg (· * b) (Nat.sub_add_cancel hh)
      simp only [Nat.add_mul] at he
      omega
    apply scalar_iff.mpr
    refine ⟨b-1-u, a-1-v, ?_⟩
    have hu' : (b-1-u)+u+1=b := by omega
    have hv' : (a-1-v)+v+1=a := by omega
    have eu := congrArg (· * a) hu'
    have ev := congrArg (· * b) hv'
    simp only [Nat.add_mul, Nat.one_mul] at eu ev
    dsimp [frob] at ht ⊢
    have hf : a*b-a-b + b + a = a*b := by omega
    have hft := Nat.sub_add_cancel ht
    nlinarith only [huv, eu, ev, hf, hft]

theorem penultimate_mem {a b : ℕ} (ha : 2 ≤ a) (hb : a < b) (hc : a.Coprime b) :
    frob a b - 1 ∈ scalar a b :=
  (reflect_mem ha hb hc (by have := bound_add ha hb; dsimp [frob]; omega)).2 (one_gap ha hb)

end TaskP.GradedWilf
