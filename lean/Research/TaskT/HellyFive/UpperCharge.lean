import Research.TaskT.HellyFive.Midpoints
import Research.TaskT.HellyFive.FiniteGeometry

namespace TaskT.HellyFive.UpperFive
open Finset
abbrev Color (n : ℕ) := Fin n → ZMod 2
def residue {n : ℕ} (z : Grid n) : Color n := fun i => z i

theorem same_of_residue {n : ℕ} {a b : Grid n} (h : residue a = residue b) : sameParity a b := by
  intro i
  exact (ZMod.intCast_eq_intCast_iff' _ _ 2).mp (congrFun h i)

def recover {n : ℕ} (m : Finset (Grid n)) : Finset (Grid n) :=
  m.image fun p => (∑ q ∈ m, q) - p - p

theorem midpoint_left_inj {n : ℕ} {a b c : Grid n} (hab : sameParity a b)
    (hac : sameParity a c) (he : gridMid a b = gridMid a c) : b = c := by
  funext i
  have h₁ := double_gridMid hab i
  have h₂ := double_gridMid hac i
  have hi := congrFun he i
  omega

theorem midpoint_comm {n : ℕ} (a b : Grid n) : gridMid a b = gridMid b a := by
  funext i
  simp [gridMid, add_comm]

theorem recover_triangle {n : ℕ} {a b c : Grid n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hrab : residue a = residue b) (hrac : residue a = residue c) :
    let u := gridMid a b
    let v := gridMid a c
    let w := gridMid b c
    let m : Finset (Grid n) := {u,v,w}
    m.card = 3 ∧ recover m = {a,b,c} ∧ residue (∑ p ∈ m, p) = residue a := by
  dsimp only
  let u := gridMid a b
  let v := gridMid a c
  let w := gridMid b c
  have ab := same_of_residue hrab
  have ac := same_of_residue hrac
  have bc := same_of_residue (hrab.symm.trans hrac)
  have uv : u ≠ v := fun hu => hbc (midpoint_left_inj ab ac hu)
  have uw : u ≠ w := by
    intro h
    apply hac
    apply midpoint_left_inj (same_of_residue hrab.symm) bc
    rwa [midpoint_comm b a]
  have vw : v ≠ w := by
    intro h
    apply hab
    apply midpoint_left_inj (same_of_residue hrac.symm) (same_of_residue (hrac.symm.trans hrab))
    rwa [midpoint_comm c a, midpoint_comm c b]
  have hu : u + v - w = a := recover_vertex ab ac bc
  have hv : u + w - v = b := by
    simpa only [u,v,w,midpoint_comm b a] using
      (recover_vertex (same_of_residue hrab.symm) bc ac)
  have hw : v + w - u = c := by
    simpa only [u,v,w,midpoint_comm c a,midpoint_comm c b] using
      (recover_vertex (same_of_residue hrac.symm) (same_of_residue (hrac.symm.trans hrab)) ab)
  have hs : (∑ p ∈ ({u,v,w} : Finset _), p) = u+v+w := by simp [uv,uw,vw,add_assoc]
  change ({u,v,w} : Finset _).card = 3 ∧ recover {u,v,w} = {a,b,c} ∧ _
  refine ⟨by simp [uv,uw,vw], ?_, ?_⟩
  · simp only [recover,hs,Finset.image_insert,Finset.image_singleton]
    have e₁ : u+v+w-u-u=c := by rw [← hw]; abel
    have e₂ : u+v+w-v-v=b := by rw [← hv]; abel
    have e₃ : u+v+w-w-w=a := by rw [← hu]; abel
    rw [e₁,e₂,e₃]; ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · change residue (∑ p ∈ ({u,v,w} : Finset _), p) = residue a
    rw [hs,← hu]
    funext i
    change (((u i + v i + w i : ℤ) : ZMod 2)) = (((u i + v i - w i : ℤ) : ZMod 2))
    apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr
    omega

def fiber {n : ℕ} (s : Finset (Grid n)) (r : Color n) : Finset (Grid n) :=
  s.filter fun p => residue p = r

def weight {n : ℕ} (X : Finset (Grid n)) (r : Color n) : ℕ :=
  ((X.powersetCard 3).filter fun m => residue (∑ p ∈ m, p) = r).card

theorem charge {n : ℕ} {s X : Finset (Grid n)} (r : Color n)
    (closure : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → sameParity a b → gridMid a b ∈ X) :
    (fiber s r).card.choose 3 ≤ weight X r := by
  let W := (X.powersetCard 3).filter fun m => residue (∑ p ∈ m, p) = r
  have sub : (fiber s r).powersetCard 3 ⊆ W.image recover := by
    intro t ht
    obtain ⟨hts,hcard⟩ := Finset.mem_powersetCard.mp ht
    obtain ⟨a,b,c,hab,hac,hbc,he⟩ := Finset.card_eq_three.mp hcard
    subst t
    have ha := Finset.mem_filter.mp (hts (by simp : a ∈ ({a,b,c}:Finset _)))
    have hb := Finset.mem_filter.mp (hts (by simp : b ∈ ({a,b,c}:Finset _)))
    have hc := Finset.mem_filter.mp (hts (by simp : c ∈ ({a,b,c}:Finset _)))
    let m : Finset _ := {gridMid a b, gridMid a c, gridMid b c}
    obtain ⟨h₁,h₂,h₃⟩ := recover_triangle hab hac hbc (ha.2.trans hb.2.symm) (ha.2.trans hc.2.symm)
    apply Finset.mem_image.mpr
    refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_,h₁⟩,h₃.trans ha.2⟩,h₂⟩
    intro p hp
    change p ∈ ({gridMid a b,gridMid a c,gridMid b c} : Finset _) at hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact closure _ ha.1 _ hb.1 hab (same_of_residue (ha.2.trans hb.2.symm))
    · exact closure _ ha.1 _ hc.1 hac (same_of_residue (ha.2.trans hc.2.symm))
    · exact closure _ hb.1 _ hc.1 hbc (same_of_residue (hb.2.trans hc.2.symm))
  rw [← Finset.card_powersetCard]
  exact (Finset.card_le_card sub).trans Finset.card_image_le

theorem card_sum_fibers {n : ℕ} (s : Finset (Grid n)) : s.card = ∑ r, (fiber s r).card :=
  Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

theorem choose_lower (m : ℕ) : m ≤ 2 + m.choose 3 := by
  induction m with
  | zero => decide
  | succ m ih =>
    by_cases h : m<2
    · omega
    · have := Nat.choose_pos (k:=2) (n:=m) (by omega)
      rw [Nat.choose_succ_succ]
      change m+1 ≤ 2 + (m.choose 2 + m.choose 3)
      omega

theorem all_dimensional_bound {n : ℕ} {s X : Finset (Grid n)}
    (closure : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → sameParity a b → gridMid a b ∈ X) :
    s.card ≤ 2 * 2^n + X.card.choose 3 := by
  rw [card_sum_fibers]
  calc
    ∑ r, (fiber s r).card ≤ ∑ r : Color n, (2 + weight X r) :=
      Finset.sum_le_sum fun r _ => (choose_lower _).trans (Nat.add_le_add_left (charge r closure) 2)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      have h : (X.powersetCard 3).card = ∑ r : Color n, weight X r :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      rw [← h,Finset.card_powersetCard]
      simp [Color, Nat.mul_comm]

end TaskT.HellyFive.UpperFive
