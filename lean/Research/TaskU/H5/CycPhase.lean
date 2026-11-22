import Research.TaskU.H5.CycNorm

namespace TaskU.H5.Cyc5

/-- The five monomials reduced modulo Φ₅. -/
def rootAt (k : ZMod 5) : V :=
  match k.val with
  | 0 => scalar 1
  | 1 => root
  | 2 => ⟨0,0,1,0⟩
  | 3 => ⟨0,0,0,1⟩
  | _ => ⟨-1,-1,-1,-1⟩

lemma rootAt_add : ∀ i j : ZMod 5, mul (rootAt i) (rootAt j) = rootAt (i+j) := by decide

local instance : Std.Associative mul := ⟨mul_assoc⟩
local instance : Std.Commutative mul := ⟨mul_comm⟩

private lemma mul_neg (v w : V) : mul (neg v) w = neg (mul v w) := by
  ext <;> simp [neg,mul] <;> ring

/-- Trace of the absolute square, expressed by the differences of five integral coefficients. -/
def energy (v : V) : ℤ := v.a^2 + v.b^2 + v.c^2 + v.d^2 +
  (v.a-v.b)^2 + (v.a-v.c)^2 + (v.a-v.d)^2 +
  (v.b-v.c)^2 + (v.b-v.d)^2 + (v.c-v.d)^2

private lemma energy_of_unitary (v : V) (h : mul v (conj v) = scalar 1) : energy v = 4 := by
  let tr (z : V) := 4*z.a-z.b-z.c-z.d
  have idn : energy v = tr (mul v (conj v)) := by simp [tr,energy,mul,conj]; ring
  rw [idn,h]; rfl

private lemma coord_bounds (v : V) (he : energy v = 4) :
    (-2 ≤ v.a ∧ v.a ≤ 2) ∧ (-2 ≤ v.b ∧ v.b ≤ 2) ∧
    (-2 ≤ v.c ∧ v.c ≤ 2) ∧ (-2 ≤ v.d ∧ v.d ≤ 2) := by
  have bound (n : ℤ) (hn : n^2 ≤ 4) : -2 ≤ n ∧ n ≤ 2 := by
    constructor
    · by_contra! h; nlinarith [sq_nonneg (n + 3)]
    · by_contra! h; nlinarith [sq_nonneg (n - 3)]
  unfold energy at he
  have h₁ := sq_nonneg (v.a-v.b)
  have h₂ := sq_nonneg (v.a-v.c)
  have h₃ := sq_nonneg (v.a-v.d)
  have h₄ := sq_nonneg (v.b-v.c)
  have h₅ := sq_nonneg (v.b-v.d)
  have h₆ := sq_nonneg (v.c-v.d)
  exact ⟨bound _ (by linarith [sq_nonneg v.b,sq_nonneg v.c,sq_nonneg v.d]),
    bound _ (by linarith [sq_nonneg v.a,sq_nonneg v.c,sq_nonneg v.d]),
    bound _ (by linarith [sq_nonneg v.a,sq_nonneg v.b,sq_nonneg v.d]),
    bound _ (by linarith [sq_nonneg v.a,sq_nonneg v.b,sq_nonneg v.c])⟩

private def centered (j : Fin 5) : ℤ := (j.val : ℤ)-2

private lemma centered_surj (n : ℤ) (h : -2 ≤ n ∧ n ≤ 2) : ∃ j : Fin 5, n=centered j := by
  refine ⟨⟨(n+2).toNat, by omega⟩,?_⟩
  simp [centered]; omega

set_option maxRecDepth 10000 in
private lemma finite_energy : ∀ a b c d : Fin 5,
    let v := V.mk (centered a) (centered b) (centered c) (centered d)
    energy v = 4 → ∃ k : ZMod 5, v=rootAt k ∨ v=neg (rootAt k) := by decide +kernel

private lemma signed_root (v : V) (h : mul v (conj v)=scalar 1) :
    ∃ k, v = rootAt k ∨ v = neg (rootAt k) := by
  have he := energy_of_unitary v h
  obtain ⟨ha,hb,hc,hd⟩ := coord_bounds v he
  obtain ⟨a,ha⟩ := centered_surj _ ha
  obtain ⟨b,hb⟩ := centered_surj _ hb
  obtain ⟨c,hc⟩ := centered_surj _ hc
  obtain ⟨d,hd⟩ := centered_surj _ hd
  have hv : v = ⟨centered a, centered b, centered c, centered d⟩ := V.ext ha hb hc hd
  rw [hv] at he ⊢
  exact finite_energy a b c d he

def residue (v : V) : ZMod 5 := (sumCoeff v : ℤ)

lemma residue_mul (v w : V) : residue (mul v w) = residue v * residue w := by
  have h : sumCoeff (mul v w) = sumCoeff v*sumCoeff w - 5*(v.b*w.d+v.c*w.c+v.d*w.b) := by
    simp [sumCoeff,mul]; ring
  simp only [residue,h,Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
  rw [show (5:ZMod 5)=0 by decide]; ring

lemma residue_conj (v : V) : residue (conj v) = residue v := by
  have h : sumCoeff (conj v) = sumCoeff v - 5*v.b := by simp [sumCoeff,conj]; ring
  simp only [residue,h,Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
  rw [show (5:ZMod 5)=0 by decide]; ring

lemma unit_phase (u : V) (hu : norm u=1) : ∃ k, conj u = mul (rootAt k) u := by
  let pair := mul (sigma2 u) (sigma3 u)
  let q := mul (conj u) (mul (conj u) pair)
  have hc : conj pair = pair := by
    simp only [pair,conj_mul,sigma3,conj_conj]; ac_rfl
  have hn : mul (mul u (conj u)) pair = scalar 1 := by rw [← hu]; exact norm_prod u
  have hqu : mul q u = conj u := by
    calc mul q u = mul (conj u) (mul (mul u (conj u)) pair) := by dsimp [q]; ac_rfl
         _ = conj u := by rw [hn,mul_scalar_one]
  have hq : mul q (conj q) = scalar 1 := by
    calc mul q (conj q) = mul (mul (mul u (conj u)) pair) (mul (mul u (conj u)) pair) := by
           simp only [q,conj_mul,conj_conj,hc]; ac_rfl
         _ = scalar 1 := by rw [hn,mul_scalar_one]
  obtain ⟨k,hk | hk⟩ := signed_root q hq
  · exact ⟨k,by rw [← hqu,hk]⟩
  · have hnz : residue u ≠ 0 := by
      intro hz
      have hp := norm_mod_five u
      change (sumCoeff u : ZMod 5) = 0 at hz
      rw [hu,hz] at hp
      norm_num at hp
      exact (by decide : (1:ZMod 5) ≠ 0) hp
    have hr := congrArg residue hqu
    rw [residue_mul,residue_conj,hk] at hr
    have hn₁ : ∀ i : ZMod 5, residue (neg (rootAt i)) = -1 := by decide
    rw [hn₁] at hr
    exfalso
    exact (by decide : ∀ x : ZMod 5, x ≠ 0 → (-1)*x ≠ x) _ hnz hr

lemma ordinary_phase (v u : V) (hv : v=mul pi u) (hu : norm u=1) :
    ∃ k : ZMod 5, conj v = neg (mul (rootAt k) v) := by
  obtain ⟨k,hk⟩ := unit_phase u hu
  have hπ : conj pi = neg (mul (rootAt (-1)) pi) := by decide
  refine ⟨-1+k,?_⟩
  rw [hv,conj_mul,hπ,hk,mul_neg,← rootAt_add]
  congr 1; ac_rfl

end TaskU.H5.Cyc5
