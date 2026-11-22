import Research.TaskU.H5B.LiftRing
import Research.TaskU.H5.RayMoments
import Research.TaskU.H5.IntegerFactors

namespace TaskU.H5.BTrace
noncomputable section
open Finset
open Cyc5 (V)
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def tr (v : V) : ℤ := 4*v.a-v.b-v.c-v.d

private theorem char_sum_erase (n : F) (h : n ≠ 0) :
    ∑ i ∈ (Finset.univ : Finset F).erase 0, ch (n*i) = -1 := by
  have hsum := orthog n
  rw [← Finset.add_sum_erase _ _ (mem_univ (0:F)), ite_eq_right h] at hsum
  simp only [mul_zero,AddChar.map_zero_eq_one] at hsum
  linear_combination hsum

theorem eval_trace (v : V) :
    ∑ r ∈ (Finset.univ : Finset F).erase 0, Cyc5.val v (ch r) = (tr v : ℂ) := by
  have h1 : ∑ r ∈ (Finset.univ : Finset F).erase 0, ch r = -1 := by
    simpa using char_sum_erase 1 (by decide)
  have h2 (r : F) : ch r ^ 2 = ch (2*r) := by simpa using Cyc5.character_pow r 2
  have h3 (r : F) : ch r ^ 3 = ch (3*r) := by simpa using Cyc5.character_pow r 3
  simp only [Cyc5.val,h2,h3, sum_add_distrib, ←mul_sum, sum_const,
    h1, char_sum_erase 2 (by decide), char_sum_erase 3 (by decide)]
  rw [show ((univ : Finset F).erase 0).card = 4 by decide]
  push_cast [tr]
  ring

theorem trace_row (f : H → ℤ) :
    (∑ v ∈ (univ : Finset F).erase 0, ∏ u : F, linearFactor f u v) =
      (tr (∏ j : F, ray f j 1) : ℂ) := by
  rw [← eval_trace]
  apply sum_congr rfl
  intro r hr
  have hn := ne_of_mem_erase hr
  let ev := Cyc5.valueHom (ch r) (Cyc5.character_rel r hn)
  change _ = ev (∏ j, ray f j 1)
  rw [map_prod]
  have reindex : (∏ j : F, linearFactor f (r*j) r) = ∏ u : F, linearFactor f u r :=
    Equiv.prod_comp (Equiv.mulLeft₀ r hn) (fun u => linearFactor f u r)
  rw [← reindex]
  apply prod_congr rfl
  intro j _
  change linearFactor f (r*j) r = Cyc5.val (ray f j 1) (ch r)
  simpa only [mul_one] using (val_ray f j 1 r hn).symm

private def conjHom : V →* V where
  toFun := Cyc5.conj
  map_mul' := Cyc5.conj_mul
  map_one' := by decide

private theorem root_sum (k : F → F) (s : Finset F) :
    ∏ i ∈ s, Cyc5.rootAt (k i) = Cyc5.rootAt (∑ i ∈ s, k i) := by
  induction s using Finset.induction_on with
  | empty => simp; rfl
  | @insert i s hi ih =>
    simp only [prod_insert hi,sum_insert hi,ih]
    exact Cyc5.rootAt_add _ _

theorem exact_trace_zero (y : F → V) (k : F → F) (hs : ∑j,k j=0)
    (hk : ∀ j, Cyc5.conj (y j) = -(Cyc5.rootAt (k j) * y j)) :
    tr (∏j,y j) = 0 := by
  have h : Cyc5.conj (∏j,y j) = -(∏j,y j) := by
    change conjHom _ = _
    rw [map_prod]
    change (∏j, Cyc5.conj (y j)) = _
    simp_rw [hk]
    rw [prod_neg,prod_mul_distrib,root_sum,hs]
    change (-1:V)^5*(1*(∏j,y j))=_
    ring
  have hc (z : V) : tr (Cyc5.conj z) = tr z := by simp [tr,Cyc5.conj]; ring
  have hn (z : V) : tr (-z) = -tr z := by simp [tr,Cyc5.neg_def,Cyc5.neg]; ring
  have ht := congrArg tr h
  rw [hc,hn] at ht; omega

private theorem prod_congr_five (x y : F → V) (s : Finset F)
    (h : ∀i, ∃a : V, x i = y i + 5*a) :
    ∃w : V, (∏i ∈ s,x i) = (∏i ∈ s,y i)+5*w := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨a,ha⟩ := h i
    obtain ⟨b,hb⟩ := ih
    refine ⟨a*(∏j ∈ s,y j)+y i*b+5*a*b,?_⟩
    rw [prod_insert hi,prod_insert hi,ha,hb]
    ring

theorem trace_replacement (x y : F → V) (h : ∀ i, ∃a : V, x i = y i+5*a) :
    (125:ℤ) ∣ tr (∏j,Cyc5.pi*x j) - tr (∏j,Cyc5.pi*y j) := by
  obtain ⟨a,ha⟩ := prod_congr_five x y univ h
  have hp : Cyc5.pi ^ 4 = 5*(⟨0,-1,1,-1⟩:V) := by decide +kernel
  let z := (⟨0,-1,1,-1⟩:V)*a
  have he : (∏j,Cyc5.pi*x j) = (∏j,Cyc5.pi*y j) + 25*(Cyc5.pi*z) := by
    simp only [prod_mul_distrib, prod_const,card_univ,ZMod.card,ha]
    rw [pow_succ Cyc5.pi 4,hp]
    dsimp only [z]
    ring
  have ht (t z : V) : tr (t+25*(Cyc5.pi*z)) - tr t = 125*z.a := by
    change tr (Cyc5.add t (Cyc5.mul (Cyc5.scalar 25) (Cyc5.mul Cyc5.pi z))) - tr t = _
    simp [tr,Cyc5.add,Cyc5.mul,Cyc5.pi,Cyc5.scalar]
    ring
  exact ⟨z.a,by rw [he,ht]⟩

end
end TaskU.H5.BTrace
