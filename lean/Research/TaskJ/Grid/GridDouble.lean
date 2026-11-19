import Research.TaskJ.Grid.GridPathEdges
import Research.TaskJ.Grid.GridSymmetry
import Research.TaskJ.Grid.GridEndpoints

namespace Grid.Double

open Challenge Grid.Pad

private theorem edgesAppend {α : Type*} : ∀ (l r : List α),
    pathEdges (l ++ r) = pathEdges l ++ (l.getLast?.toList.zip r.head?.toList) ++ pathEdges r
  | [], r => by simp [pathEdges]
  | [a], [] => by simp [pathEdges]
  | [a], b :: bs => by rfl
  | a :: b :: bs, r => by
    change (a,b) :: pathEdges ((b :: bs) ++ r) =
      (a,b) :: ((pathEdges (b :: bs) ++ _) ++ _)
    exact congrArg ((a,b) :: ·) (edgesAppend (b :: bs) r)

private theorem edgesReverse {α : Type*} : ∀ l : List α,
    pathEdges l.reverse = (pathEdges l).reverse.map Prod.swap
  | [] | [_] => rfl
  | a :: b :: bs => by
    rw [List.reverse_cons, edgesAppend, edgesReverse (b::bs)]
    simp [pathEdges, List.reverse_cons]

private theorem edgeEndpoints {α : Type*} {l : List α} {a b : α}
    (h : (a,b) ∈ pathEdges l) : a ∈ l ∧ b ∈ l := by
  obtain ⟨pre,post,rfl⟩ := split_at_edge _ _ _ h
  simp

def firstLift (anchor : Point → Bool) (v : Point) : Point := (anchor v).toNat :: v

def secondLift (ds : List ℕ) (anchor : Point → Bool) (v : Point) : Point :=
  (anchor v).toNat :: antipode ds v

def doubled (ds : List ℕ) (anchor : Point → Bool) (p : List Point) : List Point :=
  (p.map (firstLift anchor)) ++ (p.map (secondLift ds anchor)).reverse

private theorem coverLayers (anchor : Point → Bool) (p : List Point) :
    ((p.map (firstLift anchor)) ++ (p.map (fun v => (!anchor v).toNat :: v))).Perm
    ((p.map (0::·)) ++ (p.map (1::·))) := by
  induction p with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons, List.cons_append]
    apply (List.perm_middle.cons _).trans
    apply List.Perm.trans _ (List.perm_middle.symm.cons _)
    cases h : anchor v <;> simp only [firstLift, h, Bool.toNat, Bool.not_false,
      Bool.not_true] <;> first | exact (ih.cons _).cons _ | exact (List.Perm.swap _ _ _).trans ((ih.cons _).cons _)

private theorem reflectedOrder {ds : List ℕ} {p : List Point} (hp : Order ds p) :
    (p.map (antipode ds)).Perm p := by
  have hn := hp.nodup_iff.mpr (vertices_nodup ds)
  have hm : ∀ v ∈ p, v ∈ vertices ds := fun _ h => hp.mem_iff.mp h
  apply (List.perm_ext_iff_of_nodup _ hn).mpr
  · intro x
    constructor
    · intro h
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
      exact hp.mem_iff.mpr (antipode_mem (hm _ hv))
    · intro h
      exact List.mem_map.mpr ⟨_, hp.mem_iff.mpr (antipode_mem (hm _ h)),
        antipode_involutive (hm _ h)⟩
  · apply (List.nodup_map_iff_inj_on hn).mpr
    intro x hx y hy h
    calc
      x = antipode ds (antipode ds x) := (antipode_involutive (hm _ hx)).symm
      _ = antipode ds (antipode ds y) := congrArg _ h
      _ = y := antipode_involutive (hm _ hy)

theorem doubledOrder {ds : List ℕ} {p : List Point} {anchor : Point → Bool}
    (hp : Order ds p) (ha : ∀ v ∈ vertices ds, anchor (antipode ds v) = !anchor v) :
    Order (2::ds) (doubled ds anchor p) := by
  let g : Point → Point := fun v => (!anchor v).toNat :: v
  have he : p.map (secondLift ds anchor) = (p.map (antipode ds)).map g := by
    rw [List.map_map]
    apply List.map_congr_left
    intro v hv
    simp [secondLift, g, ha v (hp.mem_iff.mp hv)]
  have half : (p.map (secondLift ds anchor)).reverse.Perm (p.map g) :=
    (List.reverse_perm _).trans (he ▸ (reflectedOrder hp).map g)
  apply (half.append_left _).trans
  apply (coverLayers anchor p).trans
  simpa [vertices, List.range_succ] using ((hp.map (0::·)).append (hp.map (1::·)))

private def forwardEdge (a : Point → Bool) (e : Point × Point) : Point × Point :=
  (firstLift a e.1, firstLift a e.2)

private def backwardEdge (ds : List ℕ) (a : Point → Bool) (e : Point × Point) : Point × Point :=
  (secondLift ds a e.2, secondLift ds a e.1)

private theorem doubledEdges {ds : List ℕ} {p : List Point} {a : Point → Bool} {v : Point}
    (hv : p.getLast? = some v) :
    pathEdges (doubled ds a p) =
      ((pathEdges p).map (forwardEdge a) ++ [(firstLift a v, secondLift ds a v)]) ++
      ((pathEdges p).map (backwardEdge ds a)).reverse := by
  simp [doubled, edgesAppend, edgesReverse, pathEdges_map, hv, List.map_map,
    Function.comp_def]
  rfl

theorem endpoints (ds : List ℕ) (a : Point → Bool) (p : List Point) :
    (doubled ds a p).head? = p.head?.map (firstLift a) ∧
    (doubled ds a p).getLast? = p.head?.map (secondLift ds a) := by
  cases p with
  | nil => simp [doubled]
  | cons v vs =>
    simp only [doubled, List.head?_append, List.getLast?_append, List.head?_reverse,
      List.getLast?_reverse, List.head?_map, List.getLast?_map, List.head?_cons, Option.map_some,
      Option.some_or, and_self]

private theorem oppositeAxis (a b : Bool) (h : a ≠ b) :
    axisRadius 2 a.toNat + axisRadius 2 b.toNat - 2 * (Nat.dist a.toNat b.toNat : ℤ) = 0 := by
  cases a <;> cases b <;> first | exact (h rfl).elim | decide

private theorem sameAxis (a : Bool) :
    axisRadius 2 a.toNat + axisRadius 2 a.toNat - 2 * (Nat.dist a.toNat a.toNat : ℤ) = 2 := by
  cases a <;> decide

theorem firstRadius (ds : List ℕ) (a : Point → Bool) (x : Point) :
    radius (2::ds) (firstLift a x) = 1 + radius ds x := by
  rw [firstLift, radius_cons]
  cases (a x) <;> rfl

theorem secondRadius (a : Point → Bool) {ds x : Point} (hx : x ∈ vertices ds) :
    radius (2::ds) (secondLift ds a x) = 1 + radius ds x := by
  rw [secondLift, radius_cons, radius_antipode hx]
  cases (a x) <;> rfl

private theorem firstDefect {ds : List ℕ} {a : Point → Bool} {x y : Point}
    (h : a x ≠ a y) :
    defect (2::ds) (firstLift a x) (firstLift a y) = defect ds x y := by
  rw [firstLift, firstLift, defect_cons, oppositeAxis _ _ h, zero_add]

private theorem secondDefect {ds : List ℕ} {a : Point → Bool} {x y : Point}
    (hx : x ∈ vertices ds) (hy : y ∈ vertices ds) (h : a x ≠ a y) :
    defect (2::ds) (secondLift ds a y) (secondLift ds a x) = defect ds x y := by
  rw [secondLift, secondLift, defect_cons, oppositeAxis _ _ h.symm,
    zero_add, defect_antipode hy hx, defect_comm ds y x]

private theorem jointDefect (a : Point → Bool) {ds x : Point} (hx : x ∈ vertices ds) :
    defect (2::ds) (firstLift a x) (secondLift ds a x) = 2 := by
  rw [firstLift, secondLift, defect_cons, sameAxis, defect_to_antipode hx, add_zero]

private theorem matchingDefects {ds : List ℕ} {p : List Point} {a : Point → Bool}
    (hp : Order ds p) (hc : p.IsChain fun x y => a x ≠ a y)
    {e : Point × Point} (he : e ∈ pathEdges p) :
    defect (2::ds) (forwardEdge a e).1 (forwardEdge a e).2 = defect ds e.1 e.2 ∧
    defect (2::ds) (backwardEdge ds a e).1 (backwardEdge ds a e).2 = defect ds e.1 e.2 := by
  obtain ⟨x,y⟩ := e
  have ends := edgeEndpoints he
  have alt := (chain_edges _ _).mp hc _ he
  exact ⟨firstDefect alt, secondDefect (hp.mem_iff.mp ends.1) (hp.mem_iff.mp ends.2) alt⟩

theorem doubledLoss {ds : List ℕ} {p : List Point} {a : Point → Bool} {v : Point}
    (hp : Order ds p) (hv : p.getLast? = some v) (hc : p.IsChain fun x y => a x ≠ a y) :
    edgeLoss (2::ds) (doubled ds a p) = 2 * edgeLoss ds p + 2 := by
  let W : Point × Point → ℤ := fun e => defect (2 :: ds) e.1 e.2
  let w : Point × Point → ℤ := fun e => defect ds e.1 e.2
  have front : (pathEdges p).map (W ∘ forwardEdge a) = (pathEdges p).map w :=
    List.map_congr_left (fun _ he => (matchingDefects hp hc he).1)
  have back : (pathEdges p).map (W ∘ backwardEdge ds a) = (pathEdges p).map w :=
    List.map_congr_left (fun _ he => (matchingDefects hp hc he).2)
  have bridge : W (firstLift a v, secondLift ds a v) = 2 :=
    jointDefect _ (hp.mem_iff.mp (List.mem_of_getLast? hv))
  rw [edgeLoss_edges, edgeLoss_edges, doubledEdges hv]
  change (List.map W _).sum = 2 * ((pathEdges p).map w).sum + 2
  simp only [List.map_append, List.map_reverse, List.map_map, List.sum_append,
    List.sum_reverse_int, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, front, back, bridge]
  ring

theorem doubledChain {ds : List ℕ} {p : List Point} {a : Point → Bool} {v : Point}
    (hp : Order ds p) (hv : p.getLast? = some v)
    (ha : ∀ x ∈ vertices ds, a (antipode ds x) = !a x)
    (hc : p.IsChain fun x y => a x ≠ a y) :
    (doubled ds a p).IsChain (fun x y => a x.tail ≠ a y.tail) := by
  apply (chain_edges _ _).mpr
  intro e he
  rw [doubledEdges hv] at he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp he
      exact (chain_edges _ _).mp hc _ hz
    · rw [List.mem_singleton] at he
      subst e
      change a v ≠ a (antipode ds v)
      rw [ha _ (hp.mem_iff.mp (List.mem_of_getLast? hv))]
      cases a v <;> decide
  · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    obtain ⟨x,y⟩ := z
    have ⟨hx,hy⟩ := edgeEndpoints hz
    change a (antipode ds y) ≠ a (antipode ds x)
    rw [ha _ (hp.mem_iff.mp hy), ha _ (hp.mem_iff.mp hx)]
    have hxy : a x ≠ a y := (chain_edges _ _).mp hc _ hz
    simpa using hxy.symm

theorem doubledTouches {ds : List ℕ} {p : List Point} {a : Point → Bool} {v : Point}
    (hp : Order ds p) (hv : p.getLast? = some v) (hc : p.IsChain fun x y => a x ≠ a y)
    (ht : ∀ x ∈ p, Touches (fun u w => defect ds u w = 0) p x) :
    ∀ x ∈ doubled ds a p, Touches (fun u w => defect (2 :: ds) u w = 0) (doubled ds a p) x := by
  intro x hx
  change x ∈ p.map _ ++ (p.map _).reverse at hx
  rcases List.mem_append.mp hx with hf | hb
  · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hf
    obtain ⟨e,he,hzero,hinc⟩ := ht _ hz
    refine ⟨forwardEdge a e, ?_, (matchingDefects hp hc he).1.trans hzero, ?_⟩
    · rw [doubledEdges hv]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨e,he,rfl⟩))
    · rcases hinc with h|h
      · exact Or.inl (congrArg (firstLift a) h)
      · exact Or.inr (congrArg (firstLift a) h)
  · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hb)
    obtain ⟨e,he,hzero,hinc⟩ := ht _ hz
    refine ⟨backwardEdge ds a e, ?_, (matchingDefects hp hc he).2.trans hzero, ?_⟩
    · rw [doubledEdges hv]
      exact List.mem_append_right _ (List.mem_reverse.mpr (List.mem_map.mpr ⟨e,he,rfl⟩))
    · rcases hinc with h|h
      · exact Or.inr (congrArg (secondLift ds a) h)
      · exact Or.inl (congrArg (secondLift ds a) h)

theorem inheritedAnchor {ds : List ℕ} {a : Point → Bool}
    (ha : ∀ x ∈ vertices ds, a (antipode ds x) = !a x) :
    ∀ x ∈ vertices (2::ds), a (antipode (2::ds) x).tail = !a x.tail := by
  intro x hx
  obtain ⟨i,v,rfl,_,hv⟩ := vertex_cases hx
  exact ha v hv

/-- The inductive data on the central box with k even coordinates. -/
structure GoodEven (ds : List ℕ) (k : ℕ) (p : List Point) (anchor : Point → Bool) : Prop where
  order : Order ds p
  nonempty : p ≠ []
  headRadius : ∀ x, p.head? = some x → radius ds x = (k : ℤ)
  lastRadius : ∀ x, p.getLast? = some x → radius ds x = (k : ℤ)
  loss : edgeLoss ds p = 2 * ((2 : ℤ) ^ (k - 1) - 1)
  incident : ∀ x ∈ p, Touches (fun u v => defect ds u v = 0) p x
  alternates : p.IsChain (fun x y => anchor x ≠ anchor y)
  reflected : ∀ x ∈ vertices ds, anchor (antipode ds x) = !anchor x

theorem GoodEven.double {ds : List ℕ} {k : ℕ} {p : List Point} {a : Point → Bool}
    (h : GoodEven ds k p a) (hk : 1 ≤ k) :
    GoodEven (2::ds) (k+1) (doubled ds a p) (fun x => a x.tail) := by
  have hl := List.getLast?_eq_some_getLast h.nonempty
  have hh := List.head?_eq_some_head h.nonempty
  have ends := endpoints ds a p
  refine ⟨doubledOrder h.order h.reflected, ?_, ?_, ?_, ?_,
    doubledTouches h.order hl h.alternates h.incident,
    doubledChain h.order hl h.reflected h.alternates, inheritedAnchor h.reflected⟩
  · intro hz
    rw [hz,hh] at ends
    simp at ends
  · intro x hx
    rw [ends.1,hh] at hx
    have hx' : firstLift a (p.head h.nonempty) = x := Option.some.inj hx
    rw [← hx', firstRadius, h.headRadius _ hh]
    omega
  · intro x hx
    rw [ends.2,hh] at hx
    have hx' : secondLift ds a (p.head h.nonempty) = x := Option.some.inj hx
    rw [← hx', secondRadius _ (h.order.mem_iff.mp (List.head_mem h.nonempty)), h.headRadius _ hh]
    omega
  · rw [doubledLoss h.order hl h.alternates, h.loss]
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [Nat.succ_sub_one, pow_succ]
    ring

end Grid.Double
