import Research.TaskP.GeomSimplex.UCoordinates

namespace TaskP.GeomSimplex.Proof

open TaskP.GeomSimplex.Challenge

private theorem edge_cost (x y z : ℤ) (hn : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    6 ≤ max 0 (18*z + (18*x-13*y)) + max 0 (-(18*x-13*y)) +
          max 0 (-(18*z-y)) + max 0 (-y) := by
  by_contra! h
  have hz : z = 0 := by omega
  subst z
  have hy1 : -5 ≤ y := by omega
  have hy2 : y ≤ 5 := by omega
  interval_cases y <;> omega

theorem cost_nonzero (a b : Lattice 3) (hn : a ≠ b) :
    6 ≤ ∑ j, (uform a j - min (uform a j) (uform b j)) := by
  let u := a - b
  have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    by_contra! h
    apply hn
    funext i
    fin_cases i
    · exact sub_eq_zero.mp h.1
    · exact sub_eq_zero.mp h.2.1
    · exact sub_eq_zero.mp h.2.2
  have hc := edge_cost (-(u 0)) (-(u 1)) (-(u 2)) (by simpa using hne)
  simp [Fin.sum_univ_succ, uform]
  dsimp [u] at hc
  omega

theorem upperU {t k : ℕ} (ht : 0 < t) (hp : packs (dilate t (simplex verticesU)) k) :
    k ≤ 3 * t := by
  classical
  obtain ⟨a, b, hab, hc⟩ := pack_endpoints hp
  have hm (j : Fin 4) :
      -budget (t : ℤ) j ≤ ∑ i, min (uform (a i) j) (uform (b i) j) := by
    let e (i : Fin k) := decide (uform (b i) j ≤ uform (a i) j)
    have he := (dilateU_int t ht _).mp (hc e) j
    rw [form_sum] at he
    convert he using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : uform (b i) j ≤ uform (a i) j
    · simp [e, hi]
    · simp [e, hi, min_eq_left (le_of_not_ge hi)]
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hm j)
  have cost := Finset.sum_le_sum (s := Finset.univ) (fun i _ => cost_nonzero (a i) (b i) (hab i))
  simp only [Finset.sum_sub_distrib, forms_total, zero_sub, Finset.sum_neg_distrib] at cost
  rw [Finset.sum_comm] at bound
  have hbud : ∑ j : Fin 4, -budget (t : ℤ) j = -18*(t : ℤ) := by
    simp [budget]
  rw [hbud] at bound
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at cost
  omega

end TaskP.GeomSimplex.Proof
