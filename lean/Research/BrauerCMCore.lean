import Mathlib

set_option autoImplicit false

/-!
# Explicit complete mappings of square Rees 0-matrix semigroups over `ℤ/2`

Companion to `work/round6/brauer-complete/PROOF.md` (Problem 15.11 of Araújo–Bentz–Cameron–
Hendrey–Kinyon, *Complete Mappings of Semigroups*, arXiv:2608.25092v1).

`M⁰(ℤ/2, H, H, P)` is modelled as `Option (H × ZMod 2 × H)` (`none` is the zero), with product
`(i,a,l)(j,b,m) = (i, a + p + b, m)` if `P l j = some p` and `0` otherwise.
A *complete mapping* of a magma `(S, ⋆)` is a bijection `α` such that `x ↦ x ⋆ α x` is a bijection.

* `lemmaC` (PROOF.md, Lemma C): if `P` has zero diagonal, `L` is a Latin square on `H`, `ρ` is a
  permutation of `H` with `P l (ρ l) = some (s l)` and `c : H → ZMod 2` satisfies
  `c (ρ l) = c l + 1 + s l`, then the explicit map `fC` is a complete mapping.
* `lemmaB` (PROOF.md, Lemma B): if `P` has zero diagonal, `L` is a Latin square, `δ` is a
  permutation of `H` and `t : H → ZMod 2` satisfies `t (δ μ) = t μ + 1`, then `fB` is a
  complete mapping (no other entry of `P` is used).

The only `decide` calls are on closed statements about `ZMod 2`.
-/

namespace BrauerCMCore

/-- Elements of `M⁰(ℤ/2, H, H, P)`; `none` is the zero. -/
abbrev Elt (H : Type*) := Option (H × ZMod 2 × H)

variable {H : Type*}

/-- Product of the Rees 0-matrix semigroup `M⁰(ℤ/2, H, H, P)`. -/
def mul (P : H → H → Option (ZMod 2)) : Elt H → Elt H → Elt H
  | none, _ => none
  | some _, none => none
  | some (i, a, l), some (j, b, m) => (P l j).map (fun p => (i, a + p + b, m))

@[simp] lemma mul_none_left (P : H → H → Option (ZMod 2)) (y : Elt H) : mul P none y = none := by
  cases y <;> rfl

lemma mul_some_some (P : H → H → Option (ZMod 2)) (i j l m : H) (a b : ZMod 2) :
    mul P (some (i, a, l)) (some (j, b, m)) = (P l j).map (fun p => (i, a + p + b, m)) := rfl

/-- Complete mapping of a magma. -/
def IsCompleteMapping {S : Type*} (op : S → S → S) (α : S → S) : Prop :=
  Function.Bijective α ∧ Function.Bijective (fun x => op x (α x))

/-! ### Facts about `ZMod 2` -/

lemma z2_ne_eq (a x : ZMod 2) (h : a ≠ x) : a = x + 1 := by
  revert a x; decide

lemma z2_ne_one_add (a x : ZMod 2) (h : a ≠ 1 + x) : a = x := by
  revert a x; decide

lemma z2_ne_ne (a b x : ZMod 2) (ha : a ≠ x) (hb : b ≠ x) : a = b := by
  revert a b x; decide

lemma z2_one_add_ne (x : ZMod 2) : 1 + x ≠ x := by
  revert x; decide

lemma z2_add_one_ne (x : ZMod 2) : x + 1 ≠ x := by
  revert x; decide

lemma z2_c1 (x : ZMod 2) : x + 0 + (1 + x) = 1 := by
  revert x; decide

lemma z2_c2 (x s : ZMod 2) : (x + 1) + s + (x + 1 + s) = 0 := by
  revert x s; decide

lemma z2_b1 (x : ZMod 2) : (1 + x) + 0 + 1 = x := by
  revert x; decide

lemma z2_b2 (x : ZMod 2) : x + 0 + 0 = x := by
  revert x; decide

lemma z2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

/-! ### Lemma C -/

section LemmaC

variable (P : H → H → Option (ZMod 2)) (L : H → H → H) (ρ : H ≃ H) (c s : H → ZMod 2)

/-- The explicit map of Lemma C. -/
def fC : Elt H → Elt H
  | none => none
  | some (i, a, l) =>
      if a = c l then some (l, 1 + c l, L i l) else some (ρ l, c (ρ l), L i (ρ l))

lemma fC_pos (i l : H) (a : ZMod 2) (h : a = c l) :
    fC L ρ c (some (i, a, l)) = some (l, 1 + c l, L i l) := if_pos h

lemma fC_neg (i l : H) (a : ZMod 2) (h : ¬ a = c l) :
    fC L ρ c (some (i, a, l)) = some (ρ l, c (ρ l), L i (ρ l)) := if_neg h

lemma thetaC_pos (hdiag : ∀ l, P l l = some 0) (i l : H) (a : ZMod 2) (h : a = c l) :
    mul P (some (i, a, l)) (fC L ρ c (some (i, a, l))) = some (i, 1, L i l) := by
  rw [fC_pos L ρ c i l a h, mul_some_some, hdiag l]
  show some (i, a + 0 + (1 + c l), L i l) = some (i, 1, L i l)
  rw [h, z2_c1]

lemma thetaC_neg (hρ : ∀ l, P l (ρ l) = some (s l)) (hc : ∀ l, c (ρ l) = c l + 1 + s l)
    (i l : H) (a : ZMod 2) (h : ¬ a = c l) :
    mul P (some (i, a, l)) (fC L ρ c (some (i, a, l))) = some (i, 0, L i (ρ l)) := by
  rw [fC_neg L ρ c i l a h, mul_some_some, hρ l]
  show some (i, a + s l + c (ρ l), L i (ρ l)) = some (i, 0, L i (ρ l))
  rw [hc l, z2_ne_eq a (c l) h, z2_c2]

theorem fC_injective (hcol : ∀ l, Function.Injective (fun i => L i l)) :
    Function.Injective (fC L ρ c) := by
  intro x y hxy
  rcases x with _ | ⟨i, a, l⟩ <;> rcases y with _ | ⟨j, b, m⟩
  · rfl
  · by_cases h2 : b = c m
    · rw [fC_pos L ρ c j m b h2] at hxy; exact absurd hxy (by simp [fC])
    · rw [fC_neg L ρ c j m b h2] at hxy; exact absurd hxy (by simp [fC])
  · by_cases h1 : a = c l
    · rw [fC_pos L ρ c i l a h1] at hxy; exact absurd hxy (by simp [fC])
    · rw [fC_neg L ρ c i l a h1] at hxy; exact absurd hxy (by simp [fC])
  · by_cases h1 : a = c l <;> by_cases h2 : b = c m
    · rw [fC_pos L ρ c i l a h1, fC_pos L ρ c j m b h2] at hxy
      have e := Option.some.inj hxy
      have hlm : l = m := congrArg Prod.fst e
      have h3 : L i l = L j m := congrArg (fun q : H × ZMod 2 × H => q.2.2) e
      have hij : i = j := hcol l (show L i l = L j l by rw [h3, hlm])
      rw [hij, h1, h2, hlm]
    · rw [fC_pos L ρ c i l a h1, fC_neg L ρ c j m b h2] at hxy
      have e := Option.some.inj hxy
      have hlm : l = ρ m := congrArg Prod.fst e
      have h4 : 1 + c l = c (ρ m) := congrArg (fun q : H × ZMod 2 × H => q.2.1) e
      rw [← hlm] at h4
      exact absurd h4 (z2_one_add_ne _)
    · rw [fC_neg L ρ c i l a h1, fC_pos L ρ c j m b h2] at hxy
      have e := Option.some.inj hxy
      have hlm : ρ l = m := congrArg Prod.fst e
      have h4 : c (ρ l) = 1 + c m := congrArg (fun q : H × ZMod 2 × H => q.2.1) e
      rw [hlm] at h4
      exact absurd h4.symm (z2_one_add_ne _)
    · rw [fC_neg L ρ c i l a h1, fC_neg L ρ c j m b h2] at hxy
      have e := Option.some.inj hxy
      have hlm' : ρ l = ρ m := congrArg Prod.fst e
      have h3 : L i (ρ l) = L j (ρ m) := congrArg (fun q : H × ZMod 2 × H => q.2.2) e
      have hlm : l = m := ρ.injective hlm'
      have hij : i = j := hcol (ρ l) (show L i (ρ l) = L j (ρ l) by rw [h3, hlm])
      have hab : a = b := z2_ne_ne a b (c l) h1 (by rw [hlm]; exact h2)
      rw [hij, hab, hlm]

theorem thetaC_injective (hdiag : ∀ l, P l l = some 0) (hρ : ∀ l, P l (ρ l) = some (s l))
    (hc : ∀ l, c (ρ l) = c l + 1 + s l) (hrow : ∀ i, Function.Injective (L i)) :
    Function.Injective (fun x => mul P x (fC L ρ c x)) := by
  intro x y hxy
  change mul P x (fC L ρ c x) = mul P y (fC L ρ c y) at hxy
  rcases x with _ | ⟨i, a, l⟩ <;> rcases y with _ | ⟨j, b, m⟩
  · rfl
  · rw [mul_none_left] at hxy
    by_cases h2 : b = c m
    · rw [thetaC_pos P L ρ c hdiag j m b h2] at hxy; exact absurd hxy (by simp)
    · rw [thetaC_neg P L ρ c s hρ hc j m b h2] at hxy; exact absurd hxy (by simp)
  · rw [mul_none_left] at hxy
    by_cases h1 : a = c l
    · rw [thetaC_pos P L ρ c hdiag i l a h1] at hxy; exact absurd hxy (by simp)
    · rw [thetaC_neg P L ρ c s hρ hc i l a h1] at hxy; exact absurd hxy (by simp)
  · by_cases h1 : a = c l <;> by_cases h2 : b = c m
    · rw [thetaC_pos P L ρ c hdiag i l a h1, thetaC_pos P L ρ c hdiag j m b h2] at hxy
      have e := Option.some.inj hxy
      have hij : i = j := congrArg Prod.fst e
      have h3 : L i l = L j m := congrArg (fun q : H × ZMod 2 × H => q.2.2) e
      have hlm : l = m := hrow i (show L i l = L i m by rw [h3, hij])
      rw [hij, h1, h2, hlm]
    · rw [thetaC_pos P L ρ c hdiag i l a h1, thetaC_neg P L ρ c s hρ hc j m b h2] at hxy
      exact absurd (congrArg (fun q : H × ZMod 2 × H => q.2.1) (Option.some.inj hxy))
        z2_one_ne_zero
    · rw [thetaC_neg P L ρ c s hρ hc i l a h1, thetaC_pos P L ρ c hdiag j m b h2] at hxy
      exact absurd (congrArg (fun q : H × ZMod 2 × H => q.2.1) (Option.some.inj hxy)).symm
        z2_one_ne_zero
    · rw [thetaC_neg P L ρ c s hρ hc i l a h1, thetaC_neg P L ρ c s hρ hc j m b h2] at hxy
      have e := Option.some.inj hxy
      have hij : i = j := congrArg Prod.fst e
      have h3 : L i (ρ l) = L j (ρ m) := congrArg (fun q : H × ZMod 2 × H => q.2.2) e
      have hlm : l = m := ρ.injective (hrow i (show L i (ρ l) = L i (ρ m) by rw [h3, hij]))
      have hab : a = b := z2_ne_ne a b (c l) h1 (by rw [hlm]; exact h2)
      rw [hij, hab, hlm]

/-- **Lemma C** (PROOF.md): the explicit map `fC` is a complete mapping of `M⁰(ℤ/2, H, H, P)`. -/
theorem lemmaC [Finite H] (hdiag : ∀ l, P l l = some 0) (hρ : ∀ l, P l (ρ l) = some (s l))
    (hc : ∀ l, c (ρ l) = c l + 1 + s l)
    (hrow : ∀ i, Function.Injective (L i)) (hcol : ∀ l, Function.Injective (fun i => L i l)) :
    IsCompleteMapping (mul P) (fC L ρ c) :=
  ⟨Finite.injective_iff_bijective.mp (fC_injective L ρ c hcol),
    Finite.injective_iff_bijective.mp (thetaC_injective P L ρ c s hdiag hρ hc hrow)⟩

end LemmaC

/-! ### Lemma B -/

section LemmaB

variable (P : H → H → Option (ZMod 2)) (L : H → H → H) (δ : H ≃ H) (t : H → ZMod 2)

/-- The explicit map of Lemma B. -/
def fB : Elt H → Elt H
  | none => none
  | some (i, a, l) =>
      if a = 1 + t (L i l) then some (l, 1, L i l) else some (l, 0, δ (L i l))

lemma fB_pos (i l : H) (a : ZMod 2) (h : a = 1 + t (L i l)) :
    fB L δ t (some (i, a, l)) = some (l, 1, L i l) := if_pos h

lemma fB_neg (i l : H) (a : ZMod 2) (h : ¬ a = 1 + t (L i l)) :
    fB L δ t (some (i, a, l)) = some (l, 0, δ (L i l)) := if_neg h

lemma thetaB_pos (hdiag : ∀ l, P l l = some 0) (i l : H) (a : ZMod 2) (h : a = 1 + t (L i l)) :
    mul P (some (i, a, l)) (fB L δ t (some (i, a, l))) = some (i, t (L i l), L i l) := by
  rw [fB_pos L δ t i l a h, mul_some_some, hdiag l]
  show some (i, a + 0 + 1, L i l) = some (i, t (L i l), L i l)
  rw [h, z2_b1]

lemma thetaB_neg (hdiag : ∀ l, P l l = some 0) (i l : H) (a : ZMod 2)
    (h : ¬ a = 1 + t (L i l)) :
    mul P (some (i, a, l)) (fB L δ t (some (i, a, l))) = some (i, t (L i l), δ (L i l)) := by
  rw [fB_neg L δ t i l a h, mul_some_some, hdiag l]
  show some (i, a + 0 + 0, δ (L i l)) = some (i, t (L i l), δ (L i l))
  rw [z2_b2, z2_ne_one_add a _ h]

theorem fB_injective (hcol : ∀ l, Function.Injective (fun i => L i l)) :
    Function.Injective (fB L δ t) := by
  intro x y hxy
  rcases x with _ | ⟨i, a, l⟩ <;> rcases y with _ | ⟨j, b, m⟩
  · rfl
  · by_cases h2 : b = 1 + t (L j m)
    · rw [fB_pos L δ t j m b h2] at hxy; exact absurd hxy (by simp [fB])
    · rw [fB_neg L δ t j m b h2] at hxy; exact absurd hxy (by simp [fB])
  · by_cases h1 : a = 1 + t (L i l)
    · rw [fB_pos L δ t i l a h1] at hxy; exact absurd hxy (by simp [fB])
    · rw [fB_neg L δ t i l a h1] at hxy; exact absurd hxy (by simp [fB])
  · by_cases h1 : a = 1 + t (L i l) <;> by_cases h2 : b = 1 + t (L j m)
    · rw [fB_pos L δ t i l a h1, fB_pos L δ t j m b h2] at hxy
      have e := Option.some.inj hxy
      have hlm : l = m := congrArg Prod.fst e
      have h3 : L i l = L j m := congrArg (fun q : H × ZMod 2 × H => q.2.2) e
      have hij : i = j := hcol l (show L i l = L j l by rw [h3, hlm])
      rw [hij, h1, h2, hlm, hij]
    · rw [fB_pos L δ t i l a h1, fB_neg L δ t j m b h2] at hxy
      exact absurd (congrArg (fun q : H × ZMod 2 × H => q.2.1) (Option.some.inj hxy))
        z2_one_ne_zero
    · rw [fB_neg L δ t i l a h1, fB_pos L δ t j m b h2] at hxy
      exact absurd (congrArg (fun q : H × ZMod 2 × H => q.2.1) (Option.some.inj hxy)).symm
        z2_one_ne_zero
    · rw [fB_neg L δ t i l a h1, fB_neg L δ t j m b h2] at hxy
      have e := Option.some.inj hxy
      have hlm : l = m := congrArg Prod.fst e
      have h3 : δ (L i l) = δ (L j m) := congrArg (fun q : H × ZMod 2 × H => q.2.2) e
      have h4 : L i l = L j l := by rw [← hlm] at h3; exact δ.injective h3
      have hij : i = j := hcol l h4
      have ha : a = t (L i l) := z2_ne_one_add a _ h1
      have hb : b = t (L j m) := z2_ne_one_add b _ h2
      rw [ha, hb, hij, hlm]

theorem thetaB_injective (hdiag : ∀ l, P l l = some 0) (hδ : ∀ μ, t (δ μ) = t μ + 1)
    (hrow : ∀ i, Function.Injective (L i)) :
    Function.Injective (fun x => mul P x (fB L δ t x)) := by
  intro x y hxy
  change mul P x (fB L δ t x) = mul P y (fB L δ t y) at hxy
  rcases x with _ | ⟨i, a, l⟩ <;> rcases y with _ | ⟨j, b, m⟩
  · rfl
  · rw [mul_none_left] at hxy
    by_cases h2 : b = 1 + t (L j m)
    · rw [thetaB_pos P L δ t hdiag j m b h2] at hxy; exact absurd hxy (by simp)
    · rw [thetaB_neg P L δ t hdiag j m b h2] at hxy; exact absurd hxy (by simp)
  · rw [mul_none_left] at hxy
    by_cases h1 : a = 1 + t (L i l)
    · rw [thetaB_pos P L δ t hdiag i l a h1] at hxy; exact absurd hxy (by simp)
    · rw [thetaB_neg P L δ t hdiag i l a h1] at hxy; exact absurd hxy (by simp)
  · by_cases h1 : a = 1 + t (L i l) <;> by_cases h2 : b = 1 + t (L j m)
    · rw [thetaB_pos P L δ t hdiag i l a h1, thetaB_pos P L δ t hdiag j m b h2] at hxy
      have e := Option.some.inj hxy
      have hij : i = j := congrArg Prod.fst e
      have h3 : L i l = L j m := congrArg (fun q : H × ZMod 2 × H => q.2.2) e
      have hlm : l = m := hrow i (show L i l = L i m by rw [h3, hij])
      rw [hij, h1, h2, hlm, hij]
    · rw [thetaB_pos P L δ t hdiag i l a h1, thetaB_neg P L δ t hdiag j m b h2] at hxy
      have e := Option.some.inj hxy
      have h4 : t (L i l) = t (L j m) := congrArg (fun q : H × ZMod 2 × H => q.2.1) e
      have h3 : L i l = δ (L j m) := congrArg (fun q : H × ZMod 2 × H => q.2.2) e
      -- t (L i l) = t (L j m) and L i l = δ (L j m): contradiction with hδ
      rw [h3, hδ] at h4
      exact absurd h4 (z2_add_one_ne _)
    · rw [thetaB_neg P L δ t hdiag i l a h1, thetaB_pos P L δ t hdiag j m b h2] at hxy
      have e := Option.some.inj hxy
      have h4 : t (L i l) = t (L j m) := congrArg (fun q : H × ZMod 2 × H => q.2.1) e
      have h3 : δ (L i l) = L j m := congrArg (fun q : H × ZMod 2 × H => q.2.2) e
      rw [← h3, hδ] at h4
      exact absurd h4.symm (z2_add_one_ne _)
    · rw [thetaB_neg P L δ t hdiag i l a h1, thetaB_neg P L δ t hdiag j m b h2] at hxy
      have e := Option.some.inj hxy
      have hij : i = j := congrArg Prod.fst e
      have h3 : δ (L i l) = δ (L j m) := congrArg (fun q : H × ZMod 2 × H => q.2.2) e
      have hlm : l = m := hrow i (show L i l = L i m by rw [δ.injective h3, hij])
      have ha : a = t (L i l) := z2_ne_one_add a _ h1
      have hb : b = t (L j m) := z2_ne_one_add b _ h2
      rw [ha, hb, hij, hlm]

/-- **Lemma B** (PROOF.md): the explicit map `fB` is a complete mapping of `M⁰(ℤ/2, H, H, P)`. -/
theorem lemmaB [Finite H] (hdiag : ∀ l, P l l = some 0) (hδ : ∀ μ, t (δ μ) = t μ + 1)
    (hrow : ∀ i, Function.Injective (L i)) (hcol : ∀ l, Function.Injective (fun i => L i l)) :
    IsCompleteMapping (mul P) (fB L δ t) :=
  ⟨Finite.injective_iff_bijective.mp (fB_injective L δ t hcol),
    Finite.injective_iff_bijective.mp (thetaB_injective P L δ t hdiag hδ hrow)⟩

end LemmaB

end BrauerCMCore

#print axioms BrauerCMCore.lemmaC
#print axioms BrauerCMCore.lemmaB

/-! ### Audit: final statements and key definitions -/
#check @BrauerCMCore.lemmaC
#check @BrauerCMCore.lemmaB
#print BrauerCMCore.mul
#print BrauerCMCore.fC
#print BrauerCMCore.fB
#print BrauerCMCore.IsCompleteMapping
