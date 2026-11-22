import Mathlib

open scoped BigOperators
open Module
namespace TaskS.B.Rounding

def restr {R ι : Type*} [Field R] (K : Submodule R (ι → R)) (p : ι → Prop) :
    K →ₗ[R] (Subtype p → R) :=
  LinearMap.pi fun j => (LinearMap.proj j.val).comp K.subtype

def part {R ι : Type*} [Field R] (K : Submodule R (ι → R)) (p : ι → Prop) :
    Submodule R (Subtype p → R) := LinearMap.range (restr K p)

def supported {R ι : Type*} [Field R] (K : Submodule R (ι → R)) (p : ι → Prop) :
    Submodule R (Subtype p → R) :=
  LinearMap.range ((restr K p).comp (LinearMap.ker (restr K (fun j => ¬ p j))).subtype)

theorem part_iff {R ι : Type*} [Field R] {K : Submodule R (ι → R)} {p : ι → Prop}
    {u : Subtype p → R} : u ∈ part K p ↔ ∃ h ∈ K, ∀ j : Subtype p, h j = u j := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, h.property, fun _ => rfl⟩
  · rintro ⟨h, hh, hu⟩
    exact ⟨⟨h, hh⟩, funext hu⟩

theorem supported_iff {R ι : Type*} [Field R] {K : Submodule R (ι → R)} {p : ι → Prop}
    {u : Subtype p → R} : u ∈ supported K p ↔
    ∃ h ∈ K, (∀ j : Subtype p, h j = u j) ∧ ∀ j, ¬ p j → h j = 0 := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h.val.val, h.val.property, fun _ => rfl, fun j hj => congrFun h.property ⟨j,hj⟩⟩
  · rintro ⟨h, hh, hu, hz⟩
    exact ⟨⟨⟨h, hh⟩, funext fun j => hz j j.property⟩, funext hu⟩

theorem part_rank {ι : Type*} [Fintype ι] (K : Submodule ℚ (ι → ℚ)) (p : ι → Prop) :
    finrank ℚ (part K fun j => ¬ p j) + finrank ℚ (supported K p) = finrank ℚ K := by
  classical
  let f := restr K (fun j => ¬ p j)
  let g := (restr K p).comp (LinearMap.ker f).subtype
  have hg : Function.Injective g := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    funext j
    by_cases hj : p j
    · exact congrFun huv ⟨j,hj⟩
    · exact (congrFun u.property ⟨j,hj⟩).trans (congrFun v.property ⟨j,hj⟩).symm
  change finrank ℚ (LinearMap.range f) + finrank ℚ (LinearMap.range g) = _
  rw [← (LinearEquiv.ofInjective g hg).finrank_eq, LinearMap.finrank_range_add_finrank_ker]

theorem positive_split {ι : Type*} [Fintype ι] [Nonempty ι] (K : Submodule ℚ (ι → ℚ))
    (q : K) (hq : ∀ j, 0 < q.val j) (hd : finrank ℚ K ≠ 1) :
    ∃ v : K, (∀ j, 0 ≤ v.val j) ∧ (∃ j, v.val j = 0) ∧ ∃ j, 0 < v.val j := by
  classical
  have hq0 : q ≠ 0 := by
    intro h
    have hp := hq (Classical.arbitrary ι)
    simp [h] at hp
  have hns : ¬ ∀ w : K, ∃ c : ℚ, c • q = w :=
    fun h => hd ((finrank_eq_one_iff_of_nonzero' (K := ℚ) q hq0).mpr h)
  push Not at hns
  obtain ⟨w, hw⟩ := hns
  obtain ⟨k, hk⟩ := Finite.exists_min (fun j => w.val j / q.val j)
  let a := w.val k / q.val k
  let v : K := w - a • q
  have hnon (j : ι) : 0 ≤ v.val j := by
    change 0 ≤ w.val j - a * q.val j
    exact sub_nonneg.mpr ((le_div_iff₀ (hq j)).mp (hk j))
  refine ⟨v, hnon, ⟨k, ?_⟩, ?_⟩
  · change w.val k - (w.val k / q.val k) * q.val k = 0
    field_simp [(hq k).ne']
    ring
  · by_contra! h
    apply hw a
    apply Subtype.ext
    funext j
    change a * q.val j = w.val j
    have hz := le_antisymm (h j) (hnon j)
    change w.val j - a * q.val j = 0 at hz
    linarith

end TaskS.B.Rounding
