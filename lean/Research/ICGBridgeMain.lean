import Mathlib
import Research.ICGBridgeEnergy

/-!
# Spectral bridge, part 4: the genuine graph energy equals `exactEnergy`

* `icgAdj n D : Matrix (Fin n) (Fin n) ℝ` — adjacency matrix of the integral circulant graph
  `ICG(n, D)`: entry `(i, j)` is `1` iff `gcd((j - i) mod n, n) ∈ D` (`Fin` subtraction is
  subtraction mod `n`), else `0`.
* `energy A hA = ∑ i, |hA.eigenvalues i|` for a real symmetric matrix.
* `energy_icgAdj_eq` : for `p` prime, `p ≠ 3`, and `27 p² ∉ D`,
  `energy (icgAdj (27 p²) D) _ = exactEnergy p (maskOf p D)`.
* `roldan_q3_of_arith` : the q = 3 case of Roldán's Conjecture 1.3, *assuming* the arithmetic
  core statement `exactEnergy_strict` (proved in `Research/CirculantQ3.lean`).

The definitions in namespace `ICGBridge.Copy` are verbatim copies of the corresponding
definitions of `Research/CirculantQ3.lean` (checked to be definitionally equal in
`Research/ICGBridgeFinal.lean`).
-/

namespace ICGBridge

namespace Copy

/-! Verbatim copies of definitions from `Research/CirculantQ3.lean`. -/

def chosen (mask : Fin 2048) (j : Fin 11) : Bool := mask.val.testBit j.val

def star : Fin 2048 := 1445

def weightedP (p : ℤ) (a c : ℕ) : ℤ :=
  match a,c with
  | 0,0 => 0
  | 0,1 => -p*(p-1)
  | 0,2 => p*(p-1)
  | 1,0 => -p*(p-1)
  | 1,1 => (p-1)^2
  | 1,2 => p-1
  | 2,0 => p*(p-1)
  | 2,1 => p-1
  | 2,2 => 1
  | _,_ => 0

def weightedQ (b d : ℕ) : ℤ :=
  match b,d with
  | 0,0 => 0 | 0,1 => 0 | 0,2 => -18 | 0,3 => 18
  | 1,0 => 0 | 1,1 => -18 | 1,2 => 12 | 1,3 => 6
  | 2,0 => -18 | 2,1 => 12 | 2,2 => 4 | 2,3 => 2
  | 3,0 => 18 | 3,1 => 6 | 3,2 => 2 | 3,3 => 1
  | _,_ => 0

def weightedBasis (p : ℤ) (r : Fin 12) (j : Fin 11) : ℤ :=
  weightedP p (r.val / 4) (j.val / 4) * weightedQ (r.val % 4) (j.val % 4)

def weightedEigenvalue (p : ℤ) (mask : Fin 2048) (r : Fin 12) : ℤ :=
  ∑ j : Fin 11, if chosen mask j then weightedBasis p r j else 0

def exactEnergy (p : ℤ) (mask : Fin 2048) : ℤ :=
  ∑ r : Fin 12, |weightedEigenvalue p mask r|

end Copy

open ZMod Finset Matrix

/-! ### The arithmetic tables are Ramanujan sums times class sizes -/

/-- `φ(p^(2-a))` as a polynomial in `P = p`. -/
def totP (P : ℤ) (a : ℕ) : ℤ :=
  match a with
  | 0 => P * (P - 1)
  | 1 => P - 1
  | _ => 1

/-- `φ(3^(3-b))`. -/
def totQ (b : ℕ) : ℤ :=
  match b with
  | 0 => 18
  | 1 => 6
  | 2 => 2
  | _ => 1

theorem weightedBasis_eq (P : ℤ) (r : Fin 12) (j : Fin 11) :
    Copy.weightedBasis P r j =
      totP P (r.val / 4) * totQ (r.val % 4) * Lam P (j.val / 4) (j.val % 4) (r.val / 4) (r.val % 4) := by
  fin_cases r <;> fin_cases j <;>
    simp [Copy.weightedBasis, Copy.weightedP, Copy.weightedQ, totP, totQ, Lam, Sval] <;> ring

theorem weightedEigenvalue_eq (P : ℤ) (mask : Fin 2048) (r : Fin 12) :
    Copy.weightedEigenvalue P mask r =
      totP P (r.val / 4) * totQ (r.val % 4) * lamD P (Copy.chosen mask) (r.val / 4) (r.val % 4) := by
  unfold Copy.weightedEigenvalue lamD
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [weightedBasis_eq]
  split_ifs <;> simp

lemma totP_nonneg (P : ℤ) (hP : 1 ≤ P) (a : ℕ) : 0 ≤ totP P a := by
  unfold totP
  split <;> nlinarith

lemma totQ_nonneg (b : ℕ) : 0 ≤ totQ b := by
  unfold totQ
  split <;> norm_num

theorem exactEnergy_eq (P : ℤ) (hP : 1 ≤ P) (mask : Fin 2048) :
    Copy.exactEnergy P mask = ∑ r : Fin 12, totP P (r.val / 4) * totQ (r.val % 4) *
      |lamD P (Copy.chosen mask) (r.val / 4) (r.val % 4)| := by
  unfold Copy.exactEnergy
  apply Finset.sum_congr rfl
  intro r _
  rw [weightedEigenvalue_eq, abs_mul, abs_mul, abs_of_nonneg (totP_nonneg P hP _),
    abs_of_nonneg (totQ_nonneg _)]

/-- Class sizes: `φ(N / p^a 3^b) = φ(p^(2-a)) φ(3^(3-b))`. -/
theorem totient_er (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) (N : ℕ) (hN : N = p ^ 2 * 3 ^ 3)
    (r : Fin 12) :
    ((Nat.totient (N / er p r) : ℕ) : ℤ) = totP p (r.val / 4) * totQ (r.val % 4) := by
  have hr := r.isLt
  set a := r.val / 4 with ha
  set b := r.val % 4 with hb
  have ha2 : a ≤ 2 := by omega
  have hb3 : b ≤ 3 := by omega
  have hdiv : N / er p r = p ^ (2 - a) * 3 ^ (3 - b) := by
    have hpos : 0 < er p r := by unfold er; have := hp.pos; positivity
    have hmul : N = er p r * (p ^ (2 - a) * 3 ^ (3 - b)) := by
      rw [hN]
      unfold er
      rw [← ha, ← hb, mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.add_sub_cancel' ha2,
        Nat.add_sub_cancel' hb3]
    rw [hmul, Nat.mul_div_cancel_left _ hpos]
  rw [hdiv, Nat.totient_mul (Nat.Coprime.pow _ _ (coprime_p_three hp hp3))]
  push_cast
  have hP : ((Nat.totient (p ^ (2 - a)) : ℕ) : ℤ) = totP p a := by
    interval_cases a
    · simp only [Nat.sub_zero, totP]
      rw [Nat.totient_prime_pow hp (by norm_num)]
      push_cast [Nat.cast_sub hp.one_le]
      ring
    · simp only [totP, show 2 - 1 = 1 from rfl, pow_one]
      rw [Nat.totient_prime hp]
      push_cast [Nat.cast_sub hp.one_le]
      ring
    · simp [totP]
  have hQ : ((Nat.totient (3 ^ (3 - b)) : ℕ) : ℤ) = totQ b := by
    interval_cases b <;> decide
  rw [hP, hQ]

/-! ### The graph -/

/-- Adjacency matrix of the integral circulant graph `ICG(n, D)` on the vertex set `Fin n`:
the entry `(i, j)` is `1` iff `gcd((j - i) mod n, n) ∈ D` and `0` otherwise
(`(j - i : Fin n)` is subtraction modulo `n`). When `n ∉ D` (e.g. when `D` consists of proper
divisors of `n`, as in all main theorems) the diagonal is zero, so this is the usual loopless
adjacency matrix; for arbitrary `D ∋ n` the matrix would have ones on the diagonal. -/
def icgAdj (n : ℕ) (D : Finset ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if Nat.gcd ((j - i : Fin n) : ℕ) n ∈ D then 1 else 0

/-- The entry of `icgAdj` written with integer arithmetic: `(j - i : Fin n) = (j - i) mod n`. -/
lemma fin_sub_val_eq_emod (n : ℕ) (i j : Fin n) :
    (((j - i : Fin n) : ℕ) : ℤ) = ((j : ℤ) - i) % n := by
  have hi := i.isLt
  have hj := j.isLt
  rcases le_or_gt (i : ℕ) j with h | h
  · rw [Fin.coe_sub_iff_le.mpr h]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    push_cast [h]
    ring
  · rw [Fin.coe_sub_iff_lt.mpr h]
    have : ((j : ℤ) - i) % n = ((j : ℤ) - i + n) % n := by
      rw [Int.add_emod_right]
    rw [this, Int.emod_eq_of_lt (by omega) (by omega)]
    push_cast [show (i : ℕ) ≤ n + j by omega]
    ring

lemma gcd_sub_comm_fin (n : ℕ) (i j : Fin n) :
    Nat.gcd ((i - j : Fin n) : ℕ) n = Nat.gcd ((j - i : Fin n) : ℕ) n := by
  have hi := i.isLt
  have hj := j.isLt
  have key : ∀ x y : Fin n, x < y →
      Nat.gcd ((x - y : Fin n) : ℕ) n = Nat.gcd ((y - x : Fin n) : ℕ) n := by
    intro x y hxy
    have hxy' : (x : ℕ) < y := hxy
    have hy := y.isLt
    rw [Fin.coe_sub_iff_lt.mpr hxy', Fin.coe_sub_iff_le.mpr hxy'.le]
    have : n + (x : ℕ) - y = n - ((y : ℕ) - x) := by omega
    rw [this, Nat.gcd_self_sub_left (by omega)]
  rcases lt_trichotomy i j with h | h | h
  · exact key i j h
  · subst h; rfl
  · exact (key j i h).symm

theorem icgAdj_isHermitian (n : ℕ) (D : Finset ℕ) : (icgAdj n D).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [icgAdj, Matrix.of_apply, star_trivial]
  simp only [gcd_sub_comm_fin n j i]

/-- Energy of a real symmetric matrix: the sum of the absolute values of its eigenvalues. -/
noncomputable def energy {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

lemma finEquiv_val (n : ℕ) [NeZero n] (x : Fin n) : (ZMod.finEquiv n x).val = (x : ℕ) := by
  cases n with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ m => rfl

lemma icgAdj_eq_connFun (n : ℕ) [NeZero n] (D : Finset ℕ) (i j : Fin n) :
    icgAdj n D i j = connFun n D ((ZMod.finEquiv n).toEquiv i - (ZMod.finEquiv n).toEquiv j) := by
  have h : Nat.gcd (((ZMod.finEquiv n) i - (ZMod.finEquiv n) j).val) n =
      Nat.gcd ((j - i : Fin n) : ℕ) n := by
    rw [← map_sub, finEquiv_val, gcd_sub_comm_fin]
  simp only [icgAdj, connFun, Matrix.of_apply, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h]

/-! ### Masks -/

lemma chosen_injective : Function.Injective (fun m : Fin 2048 => Copy.chosen m) := by
  intro m1 m2 h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 11
  · have := congrFun h ⟨i, hi⟩
    simpa [Copy.chosen] using this
  · have h2048 : (2048 : ℕ) ≤ 2 ^ i := by
      calc (2048 : ℕ) = 2 ^ 11 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le m1.isLt h2048),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le m2.isLt h2048)]

lemma chosen_bijective : Function.Bijective (fun m : Fin 2048 => Copy.chosen m) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨chosen_injective, by simp⟩

/-- The unique mask whose bits are `b`. -/
noncomputable def maskOfBits (b : Fin 11 → Bool) : Fin 2048 :=
  (Equiv.ofBijective _ chosen_bijective).symm b

lemma chosen_maskOfBits (b : Fin 11 → Bool) : Copy.chosen (maskOfBits b) = b :=
  (Equiv.ofBijective _ chosen_bijective).apply_symm_apply b

/-- The mask of a connection set: bit `j` is set iff `p^(j/4) 3^(j%4) ∈ D`. -/
noncomputable def maskOf (p : ℕ) (D : Finset ℕ) : Fin 2048 := maskOfBits (bitsOf p D)

lemma chosen_maskOf (p : ℕ) (D : Finset ℕ) : Copy.chosen (maskOf p D) = bitsOf p D :=
  chosen_maskOfBits _

/-! ### Main bridge -/

/-- The DFT side of the bridge: `∑_k ‖𝓕 connFun k‖ = exactEnergy p (maskOf p D)`. -/
theorem sum_norm_dft_eq_exactEnergy (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) [NeZero (27 * p ^ 2)]
    (D : Finset ℕ) (hND : 27 * p ^ 2 ∉ D) :
    ∑ k : ZMod (27 * p ^ 2), ‖𝓕 (fun s => ((connFun (27 * p ^ 2) D s : ℝ) : ℂ)) k‖ =
      ((Copy.exactEnergy p (maskOf p D) : ℤ) : ℝ) := by
  have hN : 27 * p ^ 2 = p ^ 2 * 3 ^ 3 := by ring
  rw [sum_norm_dft_connFun hp hp3 hN D hND,
    exactEnergy_eq p (by exact_mod_cast hp.one_le), chosen_maskOf]
  push_cast
  apply Finset.sum_congr rfl
  intro r _
  have h := totient_er p hp hp3 (27 * p ^ 2) hN r
  have h' : ((Nat.totient (27 * p ^ 2 / er p r) : ℕ) : ℝ) =
      ((totP p (r.val / 4) : ℤ) : ℝ) * ((totQ (r.val % 4) : ℤ) : ℝ) := by
    rw [← Int.cast_mul, ← h]
    push_cast
    rfl
  rw [h']

/-- **Spectral bridge.** The energy of the integral circulant graph `ICG(27 p², D)` equals the
arithmetic expression `exactEnergy p (maskOf p D)`. -/
theorem energy_icgAdj_eq (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) (D : Finset ℕ)
    (hND : 27 * p ^ 2 ∉ D) :
    energy (icgAdj (27 * p ^ 2) D) (icgAdj_isHermitian _ _) =
      ((Copy.exactEnergy p (maskOf p D) : ℤ) : ℝ) := by
  have : NeZero (27 * p ^ 2) := ⟨by have := hp.pos; positivity⟩
  unfold energy
  rw [sum_abs_eigenvalues_eq_sum_norm_dft (icgAdj (27 * p ^ 2) D) _
      (ZMod.finEquiv (27 * p ^ 2)).toEquiv (connFun (27 * p ^ 2) D)
      (icgAdj_eq_connFun (27 * p ^ 2) D),
    sum_norm_dft_eq_exactEnergy p hp hp3 D hND]

/-! ### The same graph as a mathlib `SimpleGraph.circulantGraph` on `ZMod n` -/

/-- `ICG(n, D)` as mathlib's circulant (Cayley) graph on `ZMod n` with jump set
`{s | gcd(s.val, n) ∈ D}`: `a ~ b` iff `a ≠ b` and `a - b` or `b - a` lies in the jump set. -/
def icgGraph (n : ℕ) (D : Finset ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.circulantGraph {s : ZMod n | Nat.gcd s.val n ∈ D}

instance (n : ℕ) (D : Finset ℕ) : DecidableRel (icgGraph n D).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.circulantGraph {s : ZMod n | Nat.gcd s.val n ∈ D}).Adj)

lemma gcd_neg_val (n : ℕ) [NeZero n] (x : ZMod n) : Nat.gcd (-x).val n = Nat.gcd x.val n := by
  rw [ZMod.neg_val]
  split_ifs with h
  · simp [h]
  · rw [Nat.gcd_self_sub_left (ZMod.val_lt x).le]

lemma icgGraph_adj_iff (n : ℕ) [NeZero n] (D : Finset ℕ) (hND : n ∉ D) (a b : ZMod n) :
    (icgGraph n D).Adj a b ↔ Nat.gcd (a - b).val n ∈ D := by
  simp only [icgGraph, SimpleGraph.circulantGraph_adj, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rwa [← neg_sub, gcd_neg_val] at h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    simp at h
    exact hND h

lemma icgGraph_adjMatrix_eq (n : ℕ) [NeZero n] (D : Finset ℕ) (hND : n ∉ D) (a b : ZMod n) :
    (icgGraph n D).adjMatrix ℝ a b = connFun n D ((Equiv.refl (ZMod n)) a - (Equiv.refl (ZMod n)) b) := by
  rw [SimpleGraph.adjMatrix_apply]
  simp only [connFun, Equiv.refl_apply]
  exact if_congr (icgGraph_adj_iff n D hND a b) rfl rfl

/-- **Spectral bridge, `SimpleGraph` form.** -/
theorem energy_icgGraph_eq (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) [NeZero (27 * p ^ 2)]
    (D : Finset ℕ) (hND : 27 * p ^ 2 ∉ D) :
    energy ((icgGraph (27 * p ^ 2) D).adjMatrix ℝ) (SimpleGraph.isHermitian_adjMatrix ℝ _) =
      ((Copy.exactEnergy p (maskOf p D) : ℤ) : ℝ) := by
  unfold energy
  rw [sum_abs_eigenvalues_eq_sum_norm_dft ((icgGraph (27 * p ^ 2) D).adjMatrix ℝ) _
      (Equiv.refl _) (connFun (27 * p ^ 2) D) (icgGraph_adjMatrix_eq (27 * p ^ 2) D hND),
    sum_norm_dft_eq_exactEnergy p hp hp3 D hND]

/-! ### The extremal connection set -/

/-- `D* = {1, p², 3p, 9, 9p², 27p}`, i.e. `{1, p², pq, q², p²q², pq³}` with `q = 3`. -/
def Dstar (p : ℕ) : Finset ℕ := {1, p ^ 2, 3 * p, 9, 9 * p ^ 2, 27 * p}

lemma ej_injective {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : Function.Injective (ej p) := by
  intro j j' h
  have h' := (ej_eq_iff hp hp3 (a := j.val / 4) (b := j.val % 4) j').mp h
  apply Fin.ext
  omega

/-- The set of bit positions of `star = 1445`. -/
def starBits : Finset (Fin 11) := {0, 2, 5, 7, 8, 10}

lemma Dstar_eq_image (p : ℕ) : Dstar p = Finset.image (ej p) starBits := by
  simp only [Dstar, starBits, Finset.image_insert, Finset.image_singleton, ej]
  simp only [Fin.isValue, Fin.val_zero]
  norm_num
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h | h | h) <;> subst h <;> simp [mul_comm]
  · rintro (h | h | h | h | h | h) <;> subst h <;> simp [mul_comm]

lemma bitsOf_Dstar {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    bitsOf p (Dstar p) = Copy.chosen Copy.star := by
  funext j
  simp only [bitsOf, Dstar_eq_image, (ej_injective hp hp3).mem_finset_image]
  fin_cases j <;> decide

lemma maskOf_Dstar {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : maskOf p (Dstar p) = Copy.star := by
  apply chosen_injective
  simp only [chosen_maskOf, bitsOf_Dstar hp hp3]

lemma properDivisors_rep {p : ℕ} (hp : p.Prime) {x : ℕ} (hx : x ∈ (27 * p ^ 2).properDivisors) :
    ∃ j : Fin 11, ej p j = x := by
  rw [Nat.mem_properDivisors] at hx
  have hN : 27 * p ^ 2 = p ^ 2 * 3 ^ 3 := by ring
  rw [hN] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := dvd_rep hp hx.1
  have hab : 4 * a + b < 11 := by
    by_contra hcon
    have ha2 : a = 2 := by omega
    have hb3 : b = 3 := by omega
    rw [ha2, hb3] at hx
    exact lt_irrefl _ hx.2
  refine ⟨⟨4 * a + b, hab⟩, ?_⟩
  unfold ej
  congr 2 <;> simp <;> omega

lemma Dstar_subset (p : ℕ) (hp5 : 5 ≤ p) :
    Dstar p ⊆ (27 * p ^ 2).properDivisors := by
  intro x hx
  rw [Nat.mem_properDivisors]
  simp only [Dstar, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h | h | h <;> subst h
  · exact ⟨one_dvd _, by nlinarith⟩
  · exact ⟨dvd_mul_left _ _, by nlinarith⟩
  · exact ⟨⟨9 * p, by ring⟩, by nlinarith⟩
  · exact ⟨⟨3 * p ^ 2, by ring⟩, by nlinarith⟩
  · exact ⟨⟨3, by ring⟩, by nlinarith⟩
  · exact ⟨⟨p, by ring⟩, by nlinarith⟩

lemma maskOf_ne_star {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {D : Finset ℕ}
    (hD : D ⊆ (27 * p ^ 2).properDivisors) (hne : D ≠ Dstar p) : maskOf p D ≠ Copy.star := by
  have hp3 : p ≠ 3 := by omega
  intro hm
  apply hne
  have hbits : bitsOf p D = bitsOf p (Dstar p) := by
    rw [← chosen_maskOf, ← chosen_maskOf, hm, maskOf_Dstar hp hp3]
  have hiff : ∀ j : Fin 11, ej p j ∈ D ↔ ej p j ∈ Dstar p := by
    intro j
    have := congrFun hbits j
    simpa [bitsOf] using this
  ext x
  constructor
  · intro hx
    obtain ⟨j, rfl⟩ := properDivisors_rep hp (hD hx)
    exact (hiff j).mp hx
  · intro hx
    obtain ⟨j, rfl⟩ := properDivisors_rep hp (Dstar_subset p hp5 hx)
    exact (hiff j).mpr hx

/-- **Roldán's Conjecture 1.3, case `q = 3`**, conditional on the arithmetic core
(`CirculantQ3.exactEnergy_strict`, stated here for the verbatim copies). -/
theorem roldan_q3_of_arith
    (hstrict : ∀ P : ℤ, 5 ≤ P → ∀ mask : Fin 2048, mask ≠ Copy.star →
      Copy.exactEnergy P mask < Copy.exactEnergy P Copy.star)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (D : Finset ℕ)
    (hD : D ⊆ (27 * p ^ 2).properDivisors) (hne : D ≠ Dstar p) :
    energy (icgAdj (27 * p ^ 2) D) (icgAdj_isHermitian _ _) <
      energy (icgAdj (27 * p ^ 2) (Dstar p)) (icgAdj_isHermitian _ _) := by
  have hp3 : p ≠ 3 := by omega
  have hNot : ∀ E : Finset ℕ, E ⊆ (27 * p ^ 2).properDivisors → 27 * p ^ 2 ∉ E := by
    intro E hE hmem
    have := Nat.mem_properDivisors.mp (hE hmem)
    exact lt_irrefl _ this.2
  rw [energy_icgAdj_eq p hp hp3 D (hNot D hD),
    energy_icgAdj_eq p hp hp3 (Dstar p) (hNot _ (Dstar_subset p hp5)), maskOf_Dstar hp hp3]
  exact_mod_cast hstrict p (by exact_mod_cast hp5) (maskOf p D) (maskOf_ne_star hp hp5 hD hne)

/-- `SimpleGraph` (mathlib `circulantGraph`) form of `roldan_q3_of_arith`. -/
theorem roldan_q3_graph_of_arith
    (hstrict : ∀ P : ℤ, 5 ≤ P → ∀ mask : Fin 2048, mask ≠ Copy.star →
      Copy.exactEnergy P mask < Copy.exactEnergy P Copy.star)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) [NeZero (27 * p ^ 2)] (D : Finset ℕ)
    (hD : D ⊆ (27 * p ^ 2).properDivisors) (hne : D ≠ Dstar p) :
    energy ((icgGraph (27 * p ^ 2) D).adjMatrix ℝ) (SimpleGraph.isHermitian_adjMatrix ℝ _) <
      energy ((icgGraph (27 * p ^ 2) (Dstar p)).adjMatrix ℝ)
        (SimpleGraph.isHermitian_adjMatrix ℝ _) := by
  have hp3 : p ≠ 3 := by omega
  have hNot : ∀ E : Finset ℕ, E ⊆ (27 * p ^ 2).properDivisors → 27 * p ^ 2 ∉ E := by
    intro E hE hmem
    have := Nat.mem_properDivisors.mp (hE hmem)
    exact lt_irrefl _ this.2
  rw [energy_icgGraph_eq p hp hp3 D (hNot D hD),
    energy_icgGraph_eq p hp hp3 (Dstar p) (hNot _ (Dstar_subset p hp5)), maskOf_Dstar hp hp3]
  exact_mod_cast hstrict p (by exact_mod_cast hp5) (maskOf p D) (maskOf_ne_star hp hp5 hD hne)

end ICGBridge

#print axioms ICGBridge.energy_icgAdj_eq
#print axioms ICGBridge.energy_icgGraph_eq
#print axioms ICGBridge.roldan_q3_graph_of_arith
#print axioms ICGBridge.roldan_q3_of_arith
