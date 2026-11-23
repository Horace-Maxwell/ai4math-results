import Research.TaskT.HellyFive.Midpoints

namespace TaskT.HellyFive.PlanarObstruction

theorem midsum {n : ℕ} {a b c d : Grid n} (hab : sameParity a b) (hcd : sameParity c d) :
    gridMid a b = gridMid c d ↔ a+b=c+d := by
  constructor <;> intro h <;> funext i
  · have e := congrFun h i
    change a i+b i=c i+d i
    have := double_gridMid hab i; have := double_gridMid hcd i; omega
  · have e : a i+b i=c i+d i := congrFun h i
    have := double_gridMid hab i; have := double_gridMid hcd i; omega

private def left4 : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
private def right4 : Fin 6 → Fin 4 := ![1,2,3,2,3,3]

/-- Four points in a parity class can be reordered to give two diagonals with equal sums. -/
theorem balanced_four {n : ℕ} {X : Finset (Grid n)} (hc : X.card=5)
    (v : Fin 4 → Grid n) (hv : Function.Injective v)
    (hs : ∀ i j, sameParity (v i) (v j))
    (hm : ∀ i j, i ≠ j → gridMid (v i) (v j) ∈ X) :
    ∃ w : Fin 4 → Grid n, Function.Injective w ∧ (∀ i j, sameParity (w i) (w j)) ∧
      (∀ i j, i ≠ j → gridMid (w i) (w j) ∈ X) ∧ w 0+w 1=w 2+w 3 := by
  classical
  have sorted : ∀ i, left4 i < right4 i := by decide
  have pairs : Function.Injective (fun i : Fin 6 => (left4 i,right4 i)) := by decide
  let f (i : Fin 6) : X := ⟨gridMid (v (left4 i)) (v (right4 i)),hm _ _ (sorted i).ne⟩
  obtain ⟨i,j,hij,he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp [hc])
  have e := (midsum (hs (left4 i) (right4 i)) (hs (left4 j) (right4 j))).mp (congrArg Subtype.val he)
  let a := left4 i; let b := right4 i; let c := left4 j; let d := right4 j
  change v a + v b = v c + v d at e
  have hab : a < b := sorted i
  have hcd : c < d := sorted j
  have hneq : ¬(a=c ∧ b=d) := fun h => hij (pairs (Prod.ext h.1 h.2))
  have hac : a ≠ c := by
    intro hh
    rw [hh] at e
    exact hneq ⟨hh,hv (add_left_cancel e)⟩
  have hbd : b ≠ d := by
    intro hh
    rw [hh] at e
    exact hneq ⟨hv (add_right_cancel e),hh⟩
  have had : a ≠ d := by
    intro hh
    rw [hh,add_comm (v d)] at e
    have hbc := hv (add_right_cancel e)
    omega
  have hbc : b ≠ c := by
    intro hh
    rw [hh,add_comm (v a)] at e
    have had' := hv (add_left_cancel e)
    omega
  let idx : Fin 4 → Fin 4 := ![a,b,c,d]
  have hi : Function.Injective idx := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp [idx] <;> grind
  refine ⟨v ∘ idx,hv.comp hi,fun _ _ => hs _ _,fun _ _ h => hm _ _ (hi.ne h),?_⟩
  exact e

/-- The five distinct midpoint labels of a nondegenerate diagonal configuration. -/
structure Cross {n : ℕ} (X : Finset (Grid n)) where
  point : Fin 5 → Grid n
  injective : Function.Injective point
  covers : ∀ x, x ∈ X ↔ ∃ i, point i = x
  diagonalA : ∀ i, point 1 i + point 2 i = 2 * point 0 i
  diagonalB : ∀ i, point 3 i + point 4 i = 2 * point 0 i

private def cl : Fin 5 → Fin 4 := ![0,0,1,0,1]
private def cr : Fin 5 → Fin 4 := ![1,2,3,3,2]

theorem cross_of_balanced {n : ℕ} {X : Finset (Grid n)} (hX : X.card=5)
    (v : Fin 4 → Grid n) (hv : Function.Injective v)
    (hp : ∀ i j, sameParity (v i) (v j))
    (hm : ∀ i j, i ≠ j → gridMid (v i) (v j) ∈ X) (eq : v 0+v 1=v 2+v 3) :
    Nonempty (Cross X) := by
  classical
  let f (j : Fin 5) := gridMid (v (cl j)) (v (cr j))
  have heq (k : Fin n) : v 0 k+v 1 k = v 2 k+v 3 k := congrFun eq k
  have hinj : Function.Injective f := by
    intro a b h
    have e := (midsum (hp (cl a) (cr a)) (hp (cl b) (cr b))).mp h
    have e' (k : Fin n) : v (cl a) k+v (cr a) k=v (cl b) k+v (cr b) k := congrFun e k
    fin_cases a <;> fin_cases b <;> first | rfl | skip
    all_goals exfalso
    all_goals norm_num [cl,cr,Fin.isValue] at e'
    all_goals first
      | exact (show (0:Fin 4)≠1 by decide) (hv (by funext k; have := e' k; have := heq k; omega))
      | exact (show (0:Fin 4)≠2 by decide) (hv (by funext k; have := e' k; have := heq k; omega))
      | exact (show (0:Fin 4)≠3 by decide) (hv (by funext k; have := e' k; have := heq k; omega))
      | exact (show (1:Fin 4)≠2 by decide) (hv (by funext k; have := e' k; have := heq k; omega))
      | exact (show (1:Fin 4)≠3 by decide) (hv (by funext k; have := e' k; have := heq k; omega))
      | exact (show (2:Fin 4)≠3 by decide) (hv (by funext k; have := e' k; have := heq k; omega))
  have hmem (i : Fin 5) : f i ∈ X :=
    hm _ _ ((show ∀ j, cl j ≠ cr j by decide) i)
  have hset : Finset.univ.image f = X := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hmem i
    · rw [Finset.card_image_of_injective _ hinj,hX]; simp
  refine ⟨⟨f,hinj,?_,?_,?_⟩⟩
  · intro x; rw [←hset]; simp
  · intro k
    change gridMid (v 0) (v 2) k + gridMid (v 1) (v 3) k = 2 * gridMid (v 0) (v 1) k
    have := double_gridMid (hp 0 2) k; have := double_gridMid (hp 1 3) k
    have := double_gridMid (hp 0 1) k; have := heq k; omega
  · intro k
    change gridMid (v 0) (v 3) k + gridMid (v 1) (v 2) k = 2 * gridMid (v 0) (v 1) k
    have := double_gridMid (hp 0 3) k; have := double_gridMid (hp 1 2) k
    have := double_gridMid (hp 0 1) k; have := heq k; omega

end TaskT.HellyFive.PlanarObstruction
