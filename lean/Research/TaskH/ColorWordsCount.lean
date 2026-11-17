import Research.TaskH.ColorWords

/-!
Counting the color orders of a word via the position of its missing prefix
color. This is the one-direction `≤ k` part of the original multiplicity
argument; graph transport and the second direction are handled separately.
-/

set_option autoImplicit false

namespace TaskH.ColorWords

variable {k : ℕ}

/-- An injective `(k - 1)`-tuple omits exactly one of the `k` colors. -/
theorem exists_missing_prefix_color (hk : 0 < k) (f : Fin (k - 1) → Fin k)
    (hf : Function.Injective f) :
    ∃ β : Fin k, (∀ i, f i ≠ β) ∧ ∀ c, c = β ∨ ∃ i, f i = c := by
  classical
  let S : Finset (Fin k) := Finset.univ.image f
  have hScard : S.card = k - 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hcomp : (Finset.univ \ S).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Fintype.card_fin, hScard]
    omega
  obtain ⟨β, hβ⟩ := Finset.card_eq_one.mp hcomp
  have hβmem : β ∈ Finset.univ \ S := by rw [hβ]; simp
  have hβnot : β ∉ S := (Finset.mem_sdiff.mp hβmem).2
  refine ⟨β, ?_, ?_⟩
  · intro i hi
    apply hβnot
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  · intro c
    by_cases hc : c = β
    · exact Or.inl hc
    · right
      have hcnot : c ∉ Finset.univ \ S := by
        rw [hβ]
        simpa only [Finset.mem_singleton] using hc
      have hcS : c ∈ S := by
        by_contra hn
        exact hcnot (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hcS
      exact ⟨i, hi⟩

theorem permuted_prefix_range (f : Fin (k - 1) → Fin k) (β : Fin k)
    (hmissing : ∀ i, f i ≠ β) (hcover : ∀ c, c = β ∨ ∃ i, f i = c)
    (π : Equiv.Perm (Fin k)) :
    Set.range (fun i => π (f i)) = {z | z ≠ π β} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact π.injective.ne (hmissing i)
  · intro hz
    rcases hcover (π.symm z) with hy | ⟨i, hi⟩
    · exfalso
      apply hz
      calc
        z = π (π.symm z) := (π.apply_symm_apply z).symm
        _ = π β := congrArg π hy
    · refine ⟨i, ?_⟩
      change π (f i) = z
      rw [hi, π.apply_symm_apply]

/-- Once the prefix is increasing, the rank of its missing color determines
the whole color permutation. -/
theorem perm_eq_of_missing_rank (f : Fin (k - 1) → Fin k) (β : Fin k)
    (hmissing : ∀ i, f i ≠ β) (hcover : ∀ c, c = β ∨ ∃ i, f i = c)
    (π ρ : Equiv.Perm (Fin k))
    (hπ : StrictMono (fun i => π (f i)))
    (hρ : StrictMono (fun i => ρ (f i))) (he : π β = ρ β) : π = ρ := by
  have hrange : Set.range (fun i => π (f i)) = Set.range (fun i => ρ (f i)) := by
    rw [permuted_prefix_range f β hmissing hcover π,
      permuted_prefix_range f β hmissing hcover ρ, he]
  have hpref : (fun i => π (f i)) = (fun i => ρ (f i)) :=
    (hπ.range_inj_of_wellFoundedLT hρ).mp hrange
  apply Equiv.ext
  intro c
  rcases hcover c with rfl | ⟨i, hi⟩
  · exact he
  · rw [← hi]
    exact congrFun hpref i

/-- At most `k` permutations can make an injective `(k - 1)`-prefix increase. -/
theorem increasing_orders_card_le (hk : 0 < k) (f : Fin (k - 1) → Fin k)
    (hf : Function.Injective f) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
      StrictMono (fun i => π (f i)))).card ≤ k := by
  classical
  obtain ⟨β, hmissing, hcover⟩ := exists_missing_prefix_color hk f hf
  calc
    (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        StrictMono (fun i => π (f i)))).card ≤ (Finset.univ : Finset (Fin k)).card := by
      apply Finset.card_le_card_of_injOn (fun π : Equiv.Perm (Fin k) => π β)
      · intro π _
        exact Finset.mem_univ _
      · intro π hπ ρ hρ he
        exact perm_eq_of_missing_rank f β hmissing hcover π ρ
          (Finset.mem_filter.mp hπ).2 (Finset.mem_filter.mp hρ).2 he
    _ = k := by simp

/-- The actual low-descent orders of the full word inject into those prefix
orders. Existence of a low-descent order supplies prefix injectivity. -/
theorem low_descent_orders_card_le (hk : 3 ≤ k) (w : ℕ → Fin k) (L b : ℕ)
    (hlen : L + 2 = k * (b + 1))
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1)) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
      descents (fun i => π (w i)) L ≤ b)).card ≤ k := by
  classical
  by_cases hex : ∃ π : Equiv.Perm (Fin k), descents (fun i => π (w i)) L ≤ b
  · obtain ⟨π₀, hπ₀⟩ := hex
    have hf := ranked_prefix_injective hk w π₀ L b hlen hne hπ₀
    calc
      (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
          descents (fun i => π (w i)) L ≤ b)).card ≤
          (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
            StrictMono (fun i : Fin (k - 1) => π (w i.val)))).card := by
        apply Finset.card_le_card
        intro π hπ
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact ranked_prefix_strictMono hk w π L b hlen hne (Finset.mem_filter.mp hπ).2
      _ ≤ k := increasing_orders_card_le (by omega) (fun i => w i.val) hf
  · have hempty : (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        descents (fun i => π (w i)) L ≤ b)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro π hπ
      exact hex ⟨π, (Finset.mem_filter.mp hπ).2⟩
    rw [hempty]
    simp

end TaskH.ColorWords

#print axioms TaskH.ColorWords.exists_missing_prefix_color
#print axioms TaskH.ColorWords.perm_eq_of_missing_rank
#print axioms TaskH.ColorWords.increasing_orders_card_le
#print axioms TaskH.ColorWords.low_descent_orders_card_le
