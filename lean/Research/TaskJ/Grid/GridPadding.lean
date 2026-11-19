import Research.TaskJ.Grid.GridSymmetry

namespace Grid.Pad

open Challenge

/-- Each pair records an inner side and the width added to either end of that axis. -/
abbrev Padding := List (ℕ × ℕ)

def inner (pads : Padding) : List ℕ := pads.map Prod.fst
def outer (pads : Padding) : List ℕ := pads.map (fun (d,b) => d + 2*b)
def shift (pads : Padding) (p : Point) : Point := List.zipWith (fun a x => a.2+x) pads p

def Wide (pads : Padding) : Prop := ∀ t ∈ pads, 2 ≤ t.1

theorem shift_mem {pads : Padding} {x : Point} (hx : x ∈ vertices (inner pads)) :
    shift pads x ∈ vertices (outer pads) := by
  induction pads generalizing x with
  | nil => simp [vertices,shift,outer]
  | cons pair pads ih =>
    rcases pair with ⟨d,b⟩
    obtain ⟨a,x,rfl,ha,hx⟩ := vertex_cases hx
    apply vertex_cons.mpr
    exact ⟨by change b+a < d+2*b; omega,ih hx⟩

theorem shift_inj {pads : Padding} {x y : Point} (hx : x ∈ vertices (inner pads))
    (hy : y ∈ vertices (inner pads)) (h : shift pads x = shift pads y) : x=y := by
  induction pads generalizing x y with
  | nil => simp [inner,vertices] at hx hy; subst_vars; rfl
  | cons t pads ih =>
    obtain ⟨a,x,rfl,_,hx⟩ := vertex_cases hx
    obtain ⟨b,y,rfl,_,hy⟩ := vertex_cases hy
    obtain ⟨hh,ht⟩ := List.cons.inj h
    exact congrArg₂ List.cons (Nat.add_left_cancel hh) (ih hx hy ht)

theorem radius_shift {pads : Padding} {x : Point} (hx : x ∈ vertices (inner pads)) :
    radius (outer pads) (shift pads x) = radius (inner pads) x := by
  induction pads generalizing x with
  | nil => rfl
  | cons t pads ih =>
    rcases t with ⟨d,b⟩
    obtain ⟨a,x,rfl,_,hx⟩ := vertex_cases hx
    apply congrArg₂ (· + ·) _ (ih hx)
    change axisRadius (d+2*b) (b+a) = axisRadius d a
    unfold axisRadius
    push_cast
    ring_nf

theorem dist_shift {pads : Padding} {x y : Point} (hx : x ∈ vertices (inner pads))
    (hy : y ∈ vertices (inner pads)) :
    manhattan (shift pads x) (shift pads y) = manhattan x y := by
  induction pads generalizing x y with
  | nil => simp [inner,vertices] at hx hy; subst_vars; rfl
  | cons t pads ih =>
    obtain ⟨a,x,rfl,_,hx⟩ := vertex_cases hx
    obtain ⟨b,y,rfl,_,hy⟩ := vertex_cases hy
    apply congrArg₂ (· + ·) _ (ih hx hy)
    change Nat.dist (t.2 + a) (t.2 + b) = Nat.dist a b
    unfold Nat.dist
    omega

theorem defect_shift {pads : Padding} {x y : Point} (hx : x ∈ vertices (inner pads))
    (hy : y ∈ vertices (inner pads)) :
    defect (outer pads) (shift pads x) (shift pads y) = defect (inner pads) x y := by
  simp [defect,radius_shift hx,radius_shift hy,dist_shift hx hy]

theorem antipode_shift {pads : Padding} {x : Point} (hx : x ∈ vertices (inner pads)) :
    antipode (outer pads) (shift pads x) = shift pads (antipode (inner pads) x) := by
  induction pads generalizing x with
  | nil => rfl
  | cons t pads ih =>
    rcases t with ⟨d,b⟩
    obtain ⟨a,x,rfl,ha,hx⟩ := vertex_cases hx
    apply congrArg₂ List.cons _ (ih hx)
    change (d+2*b)-1-(b+a) = b+(d-1-a)
    change a < d at ha
    omega

private theorem small_sign (d b a : ℕ) (hd : 2 ≤ d) :
    ∃ v < d, axisSign (d+2*b) (b+v) = axisSign (d+2*b) a := by
  by_cases h₁ : 2*a+1 < d+2*b
  · exact ⟨0, by omega, by unfold axisSign; split_ifs <;> omega⟩
  by_cases h₂ : d+2*b < 2*a+1
  · exact ⟨d-1,by omega,by simp [axisSign,h₁,h₂,
          show ¬ 2*(b+(d-1))+1 < d+2*b by omega, show d+2*b < 2*(b+(d-1))+1 by omega]⟩
  exact ⟨d/2, by omega, by simp [axisSign,h₁,h₂,show 2*(b+d/2)+1=d+2*b by omega]⟩

theorem realize_signature {pads : Padding} (hw : Wide pads) {v : Point}
    (hv : v ∈ vertices (outer pads)) :
    ∃ a ∈ vertices (inner pads), signature (outer pads) (shift pads a) = signature (outer pads) v := by
  induction pads generalizing v with
  | nil => simp [vertices,inner,outer,signature,shift]
  | cons t pads ih =>
    rcases t with ⟨d,b⟩
    obtain ⟨a,x,rfl,_,hx⟩ := vertex_cases hv
    obtain ⟨u,hu,he⟩ := small_sign d b a (hw _ (List.mem_cons_self))
    obtain ⟨w,hw',hwe⟩ := ih (fun t ht => hw t (List.mem_cons_of_mem _ ht)) hx
    exact ⟨u::w,vertex_cons.mpr ⟨hu,hw'⟩,congrArg₂ List.cons he hwe⟩

theorem central_unique {ds u v : List ℕ} (hu : u ∈ vertices ds) (hv : v ∈ vertices ds)
    (h : antipode ds u = u) (hs : signature ds u = signature ds v) : u=v := by
  induction ds generalizing u v with
  | nil => simp [vertices] at hu hv; subst_vars; rfl
  | cons d ds ih =>
    obtain ⟨a,u,rfl,ha,hu⟩ := vertex_cases hu
    obtain ⟨b,v,rfl,_,hv⟩ := vertex_cases hv
    obtain ⟨hh,ht⟩ := List.cons.inj h
    obtain ⟨sh,st⟩ := List.cons.inj hs
    apply congrArg₂ List.cons _ (ih hu hv ht st)
    change d-1-a = a at hh
    change axisSign d a = axisSign d b at sh
    unfold axisSign at sh
    split_ifs at sh <;> omega

end Grid.Pad
