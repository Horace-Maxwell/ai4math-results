import Research.Backfill.Paper1.SupplementStatements

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset

theorem check_MultiplicativeBridge : NarrowSupplement.MultiplicativeBridge := by
  intro p q a b hp hq _hpq _ha _hb D _hconn
  constructor
  · rintro ⟨A, B, hA, hB, hD⟩
    refine ⟨A.image (fun i => p ^ i), B.image (fun j => q ^ j), ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
      exact Nat.mem_divisors.mpr ⟨Nat.pow_dvd_pow p (by have := mem_range.mp (hA hi); omega),
        pow_ne_zero a hp.ne_zero⟩
    · intro v hv
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
      exact Nat.mem_divisors.mpr ⟨Nat.pow_dvd_pow q (by have := mem_range.mp (hB hj); omega),
        pow_ne_zero b hq.ne_zero⟩
    · rw [hD]
      ext z
      constructor
      · intro hz
        obtain ⟨⟨i, j⟩, hij, heq⟩ := mem_image.mp hz
        obtain ⟨hi, hj⟩ := mem_product.mp hij
        exact mem_image.mpr ⟨(p ^ i, q ^ j), mem_product.mpr
          ⟨mem_image.mpr ⟨i, hi, rfl⟩, mem_image.mpr ⟨j, hj, rfl⟩⟩, heq⟩
      · intro hz
        obtain ⟨⟨u, v⟩, huv, heq⟩ := mem_image.mp hz
        obtain ⟨hu, hv⟩ := mem_product.mp huv
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
        exact mem_image.mpr ⟨(i, j), mem_product.mpr ⟨hi, hj⟩, heq⟩
  · rintro ⟨A, B, hA, hB, hD⟩
    let I : Finset ℕ := (range (a + 1)).filter (fun i => p ^ i ∈ A)
    let J : Finset ℕ := (range (b + 1)).filter (fun j => q ^ j ∈ B)
    refine ⟨I, J, filter_subset _ _, filter_subset _ _, ?_⟩
    rw [hD]
    ext z
    constructor
    · intro hz
      obtain ⟨⟨u, v⟩, huv, heq⟩ := mem_image.mp hz
      obtain ⟨hu, hv⟩ := mem_product.mp huv
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp (hA hu)).1
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hq).mp (Nat.mem_divisors.mp (hB hv)).1
      exact mem_image.mpr ⟨(i, j), mem_product.mpr
        ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), hu⟩,
          mem_filter.mpr ⟨mem_range.mpr (by omega), hv⟩⟩, heq⟩
    · intro hz
      obtain ⟨⟨i, j⟩, hij, heq⟩ := mem_image.mp hz
      obtain ⟨hi, hj⟩ := mem_product.mp hij
      exact mem_image.mpr ⟨(p ^ i, q ^ j), mem_product.mpr
        ⟨(mem_filter.mp hi).2, (mem_filter.mp hj).2⟩, heq⟩

#print axioms check_MultiplicativeBridge
end CodexPaper1
