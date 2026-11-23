import Research.TaskT.HellyFive.UpperCharge

namespace TaskT.HellyFive.UpperFive

def indexedWeight {n : ℕ} (f : Fin 5 → Color n) (r : Color n) : ℕ :=
  (((Finset.univ : Finset (Fin 5)).powersetCard 3).filter (fun t => (∑ i ∈ t, f i) = r)).card

theorem weight_le_of_subset {n : ℕ} {X Y : Finset (Grid n)} (h : X ⊆ Y) (r : Color n) :
    weight X r ≤ weight Y r :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.powersetCard_mono h))

theorem weight_map {n : ℕ} (e : Fin 5 ↪ Grid n) (r : Color n) :
    weight (Finset.univ.map e) r = indexedWeight (fun i => residue (e i)) r := by
  unfold weight indexedWeight
  rw [Finset.powersetCard_map, Finset.filter_map, Finset.card_map]
  congr 1
  ext t
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro _
  change (residue (∑ p ∈ t.map e, p) = r) ↔ _
  rw [Finset.sum_map]
  have he : residue (∑ a ∈ t, e a) = ∑ a ∈ t, residue (e a) := by
    funext i
    simp [residue, Finset.sum_apply]
  rw [he]

theorem indexed_cover {n : ℕ} (hn : 0 < n) (X : Finset (Grid n)) (hk : X.card ≤ 5) :
    ∃ f : Fin 5 → Color n, ∀ r, weight X r ≤ indexedWeight f r := by
  classical
  let j : Fin n := ⟨0,hn⟩
  let : Infinite (Grid n) := Infinite.of_injective (fun z : ℤ => fun _ : Fin n => z)
    (fun _ _ h => congrFun h j)
  obtain ⟨Y,hXY,hY⟩ := Infinite.exists_superset_card_eq X 5 hk
  let e₀ : Fin 5 ≃ Y := (Fintype.equivFinOfCardEq (by simpa using hY)).symm
  let e : Fin 5 ↪ Grid n := e₀.toEmbedding.trans (Function.Embedding.subtype _)
  have hi : Finset.univ.map e = Y := by
    ext p
    constructor
    · intro hp
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hp
      exact (e₀ i).property
    · intro hp
      apply Finset.mem_map.mpr
      exact ⟨e₀.symm ⟨p,hp⟩,Finset.mem_univ _,congrArg Subtype.val (e₀.apply_symm_apply ⟨p,hp⟩)⟩
  exact ⟨_,fun r => (weight_le_of_subset hXY r).trans_eq ((hi ▸ weight_map e r) : weight Y r = _)⟩

def capacity (w : ℕ) : ℕ := if 10 ≤ w then 5 else if 4 ≤ w then 4 else if 1 ≤ w then 3 else 2

theorem card_le_capacity {m w : ℕ} (h : m.choose 3 ≤ w) (hw : w ≤ 10) : m ≤ capacity w := by
  have hm : m < 6 := by
    by_contra! hm
    have hbig := Nat.choose_le_choose 3 hm
    norm_num [Nat.choose] at hbig
    omega
  interval_cases m <;> simp_all [capacity, Nat.choose] <;> split_ifs <;> omega

theorem indexedWeight_le_ten {n : ℕ} (f : Fin 5 → Color n) (r : Color n) : indexedWeight f r ≤ 10 := by
  calc
    _ ≤ ((Finset.univ : Finset (Fin 5)).powersetCard 3).card := Finset.card_filter_le _ _
    _ = 10 := by decide

end TaskT.HellyFive.UpperFive
