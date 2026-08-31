module

public import SphereSixComplex.Topology.PaperSectionSevenCuspSwappedCoverRefinement
public import SphereSixComplex.Topology.PaperSectionSevenCuspSignedCoverOrientationObstruction

/-!
# Geometry audit of the fixed swapped cusp cover

The swapped labels correct the sign at the mapping-torus vertex, but the fixed Wang vertex band
extends too far around the angular circle.  At phase `5/16` its normalized cusp product lies in
the left half-plane, so the point is not in the order-four height open.  Hence the fixed swapped
refinement is also empty; a successful comparison must change the geometric cover itself.
-/

@[expose] public section

noncomputable section

open Set
open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods.ExactNormalizedModularJTau

namespace SphereSixComplex.Geometry.PaperAnalyticData

namespace SectionSevenEllipticTwoDiscCoverData

/-- A factor in a broad left sector remains in the left half-plane after multiplication by the
narrowly right-facing cusp unit. -/
public theorem mul_re_neg_of_broad_left_sector (q u : ℂ)
    (hqre : q.re < 0) (hqsector : |q.im| ≤ 50 * (-q.re))
    (husector : 100 * |u.im| < u.re) :
    (q * u).re < 0 := by
  have hure : 0 < u.re := by nlinarith [abs_nonneg u.im]
  rw [Complex.mul_re]
  calc
    q.re * u.re - q.im * u.im ≤ q.re * u.re + |q.im| * |u.im| := by
      have hcross : -(q.im * u.im) ≤ |q.im| * |u.im| := by
        rw [← abs_mul]
        exact neg_le_abs _
      linarith
    _ < q.re * u.re + (50 * (-q.re)) * (u.re / 100) := by
      have huim : |u.im| < u.re / 100 := by linarith
      have hcoef : 0 < 50 * (-q.re) := by nlinarith
      have hprod : |q.im| * |u.im| < (50 * (-q.re)) * (u.re / 100) := calc
        |q.im| * |u.im| ≤ (50 * (-q.re)) * |u.im| :=
          mul_le_mul_of_nonneg_right hqsector (abs_nonneg _)
        _ < (50 * (-q.re)) * (u.re / 100) :=
          mul_lt_mul_of_pos_left huim hcoef
      linarith
    _ < 0 := by nlinarith [mul_pos (neg_pos.mpr hqre) hure]

/-- The phase `5/16` faces left. -/
public theorem cos_two_pi_mul_five_sixteenths_neg :
    Real.cos (2 * Real.pi * (5 / 16 : ℝ)) < 0 := by
  rw [show 2 * Real.pi * (5 / 16 : ℝ) = Real.pi / 8 + Real.pi / 2 by ring,
    Real.cos_add_pi_div_two]
  have h : 0 < Real.sin (Real.pi / 8) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  linarith

/-- At phase `5/16`, the angular parameter lies well inside the broad left sector used above. -/
public theorem sin_two_pi_mul_five_sixteenths_le :
    |Real.sin (2 * Real.pi * (5 / 16 : ℝ))| ≤
      50 * (-Real.cos (2 * Real.pi * (5 / 16 : ℝ))) := by
  rw [show 2 * Real.pi * (5 / 16 : ℝ) = Real.pi / 8 + Real.pi / 2 by ring,
    Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
  have hcpos : 0 < Real.cos (Real.pi / 8) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  rw [abs_of_pos hcpos]
  have hc : Real.cos (Real.pi / 8) ≤ 1 := Real.cos_le_one _
  have hs' : (1 / 50 : ℝ) < Real.sin (Real.pi / 8) := by
    rw [Real.sin_pi_div_eight]
    have hsqrt2nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsq2 : Real.sqrt 2 < 3 / 2 := by nlinarith
    have harg : (1 / 25 : ℝ) ^ 2 < 2 - Real.sqrt 2 := by nlinarith
    have hsqrt : (1 / 25 : ℝ) < Real.sqrt (2 - Real.sqrt 2) :=
      (Real.lt_sqrt (by norm_num)).2 harg
    linarith
  nlinarith

/-- A cylinder point in the broad left sector has negative reciprocal affine height. -/
public theorem actualCuspCylinderReciprocalProduct_re_neg_of_broadLeftSector
    {A : PaperAnalyticData}
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber)
    (hcos : Real.cos (2 * Real.pi * (p.1 : ℝ)) < 0)
    (hsector : |Real.sin (2 * Real.pi * (p.1 : ℝ))| ≤
      50 * (-Real.cos (2 * Real.pi * (p.1 : ℝ)))) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    let z := circleMappingTorusCylinderProjection G.clutching p
    let a := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
    (cuspQ a.1.2 * A.actualNormalizedModularJUniformization.cusp.cuspUnit
      (cuspQ a.1.2))⁻¹.re < 0 := by
  dsimp only
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let z := circleMappingTorusCylinderProjection G.clutching p
  let a := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
  let q := cuspQ a.1.2
  have hrho : 0 < ‖q‖ := norm_cuspQ_pos _
  have hre := actualCuspAdditiveLift_cuspQ_re_eq_mappingTorusCos (A := A) p
  have him := actualCuspAdditiveLift_cuspQ_im_eq_mappingTorusSin (A := A) p
  have hqre : q.re < 0 := by
    change (cuspQ a.1.2).re < 0
    rw [hre]
    exact mul_neg_of_pos_of_neg hrho hcos
  have hqsector : |q.im| ≤ 50 * (-q.re) := by
    change |(cuspQ a.1.2).im| ≤ 50 * (-(cuspQ a.1.2).re)
    rw [hre, him, abs_mul, abs_of_pos hrho]
    nlinarith [mul_nonneg hrho.le
      (abs_nonneg (Real.sin (2 * Real.pi * (p.1 : ℝ))))]
  let u := A.actualNormalizedModularJUniformization.cusp.cuspUnit q
  have hproduct : (q * u).re < 0 :=
    mul_re_neg_of_broad_left_sector q u hqre hqsector
      (A.actualPuncturedCuspWitness_cuspUnit_narrow_right_sector q a.2)
  exact inv_re_neg_of_re_neg _ hproduct

/-- Pointwise, the fixed Wang vertex band does not map into the order-four cusp open. -/
public theorem not_actualCuspSwappedVertexPointwiseMembership
    {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ¬ (let G := A.actualCuspRadialClutchingData
       let _ := G.fiberTopology
       ∀ z : CircleMappingTorus G.clutching,
        z ∈ vertexPiece (fun _ : Unit ↦ G.clutching) →
          G.totalHomotopyEquiv.invFun z ∈ R.twoDiscCover.cuspOrderFourOpen) := by
  intro h
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  dsimp only at h
  let y : G.Fiber := additiveTorusProjection
    (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness)).1 0
  let t : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
  let p : unitInterval × G.Fiber := (t, y)
  let z : CircleMappingTorus G.clutching :=
    circleMappingTorusCylinderProjection G.clutching p
  have hzvertex : z ∈ vertexPiece (fun _ : Unit ↦ G.clutching) := by
    change bouquetMk (fun _ : Unit ↦ G.clutching) ((), t, y) ∈
      vertexPiece (fun _ : Unit ↦ G.clutching)
    rw [vertexPiece, mem_bouquetPiece_mk_iff _ vertexBand_ends]
    exact Or.inl (by norm_num [t])
  have hmem : G.totalHomotopyEquiv.invFun z ∈
      R.twoDiscCover.cuspOrderFourOpen := h z hzvertex
  have hgt := (cuspToEllipticInteriorMap_mem_orderFourSide_iff_height R _).1 hmem
  have hneg :
      A.sectionSevenEllipticCentralHeight
        ⟨R.twoDiscCover.cuspToEllipticInteriorMap (G.totalHomotopyEquiv.invFun z),
          R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage _⟩ < 0 := by
    rw [R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus z]
    exact actualCuspCylinderReciprocalProduct_re_neg_of_broadLeftSector p
      (by simpa [p, t] using cos_two_pi_mul_five_sixteenths_neg)
      (by simpa [p, t] using sin_two_pi_mul_five_sixteenths_le)
  linarith

/-- Therefore the fixed swapped refinement has no witness. -/
public theorem not_actualCuspSwappedCoverRefinement
    {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ¬ ActualCuspSwappedCoverRefinement R := by
  intro C
  apply not_actualCuspSwappedVertexPointwiseMembership R
  dsimp only
  intro z hz
  exact C.vertex_le hz

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
