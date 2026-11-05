import Research.Backfill.Paper7.C61FourTraceConstraints

/-! NEW SOURCE ONLY. Algebraic consequences of the three alternating pair
identities. These retain a free real coefficient at every original site. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four

theorem alternating_pair_coordinate_products (a c e x y z : ℝ)
    (h0 : a*x+e*y=2) (h1 : c*x+e*z=2) (h2 : c*y+a*z=2) :
    a*x*z=x+z-y ∧ c*x*y=x+y-z ∧ e*y*z=y+z-x := by
  have h0z := congrArg (fun t : ℝ => t*z) h0
  have h1y := congrArg (fun t : ℝ => t*y) h1
  have h2x := congrArg (fun t : ℝ => t*x) h2
  constructor
  · nlinarith only [h0z, h1y, h2x]
  constructor
  · nlinarith only [h0z, h1y, h2x]
  · nlinarith only [h0z, h1y, h2x]
#print axioms Paper7C61Four.alternating_pair_coordinate_products

theorem alternating_pair_sum_product (a c e x y z : ℝ)
    (h0 : a*x+e*y=2) (h1 : c*x+e*z=2) (h2 : c*y+a*z=2) :
    (a+c+e)*x*y*z = 2*x*y+2*x*z+2*y*z-x^2-y^2-z^2 := by
  obtain ⟨ha, hc, he⟩ := alternating_pair_coordinate_products a c e x y z h0 h1 h2
  have hay := congrArg (fun t : ℝ => t*y) ha
  have hcz := congrArg (fun t : ℝ => t*z) hc
  have hex := congrArg (fun t : ℝ => t*x) he
  nlinarith only [hay, hcz, hex]
#print axioms Paper7C61Four.alternating_pair_sum_product

end Paper7C61Four
