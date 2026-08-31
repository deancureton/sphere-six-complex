module

public import SphereSixComplex.Topology.PaperSectionSevenCuspMappingTorusPhaseBridge

/-!
# Orientation obstruction for the first cusp-cover refinement

The standard mapping-torus vertex lies over angular coordinate zero.  At that point the
normalized cusp product is in the narrow right sector, so its reciprocal affine height is
strictly greater than `2 / 3`.  Consequently the vertex cannot refine the order-three open.
This rules out the first proposed orientation and forces the swapped cover used by the later
comparison.
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

/-- A small complex number in the right `45°` sector has reciprocal real part greater than
`2 / 3`. -/
public theorem two_thirds_lt_inv_re_of_norm_lt_half_of_right_sector
    (z : ℂ) (hre : 0 < z.re) (hsector : |z.im| < z.re)
    (hnorm : ‖z‖ < (1 / 2 : ℝ)) :
    (2 / 3 : ℝ) < z⁻¹.re := by
  have hreNorm : z.re ≤ ‖z‖ :=
    (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have hreHalf : z.re < 1 / 2 := hreNorm.trans_lt hnorm
  have himsq : z.im ^ 2 < z.re ^ 2 := by
    have hsquare := mul_self_lt_mul_self (abs_nonneg z.im) hsector
    calc
      z.im ^ 2 = |z.im| ^ 2 := (sq_abs z.im).symm
      _ < z.re ^ 2 := by simpa only [pow_two] using hsquare
  have hnormSq : 2 * Complex.normSq z < 3 * z.re := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re]
  have hzne : z ≠ 0 := by
    intro h
    subst z
    norm_num at hre
  rw [Complex.inv_re,
    div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 3) (Complex.normSq_pos.mpr hzne)]
  simpa [mul_comm] using hnormSq

/-- A right-sector cylinder point has reciprocal affine height greater than `2 / 3`. -/
public theorem two_thirds_lt_actualCuspCylinderReciprocalProduct_re
    {A : PaperAnalyticData}
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber)
    (hcos : 0 < Real.cos (2 * Real.pi * (p.1 : ℝ)))
    (hsector : 50 * |Real.sin (2 * Real.pi * (p.1 : ℝ))| ≤
      49 * Real.cos (2 * Real.pi * (p.1 : ℝ))) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    let z := circleMappingTorusCylinderProjection G.clutching p
    let a := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
    (2 / 3 : ℝ) <
      (cuspQ a.1.2 * A.actualNormalizedModularJUniformization.cusp.cuspUnit
        (cuspQ a.1.2))⁻¹.re := by
  dsimp only
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let z := circleMappingTorusCylinderProjection G.clutching p
  let a := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
  let q := cuspQ a.1.2
  have hrho : 0 < ‖q‖ := norm_cuspQ_pos _
  have hre := actualCuspAdditiveLift_cuspQ_re_eq_mappingTorusCos (A := A) p
  have him := actualCuspAdditiveLift_cuspQ_im_eq_mappingTorusSin (A := A) p
  have hqre : 0 < q.re := by
    change 0 < (cuspQ a.1.2).re
    rw [hre]
    positivity
  have hqsector : 50 * |q.im| ≤ 49 * q.re := by
    change 50 * |(cuspQ a.1.2).im| ≤ 49 * (cuspQ a.1.2).re
    rw [hre, him, abs_mul, abs_of_pos hrho]
    nlinarith [mul_nonneg hrho.le
      (abs_nonneg (Real.sin (2 * Real.pi * (p.1 : ℝ))))]
  let u := A.actualNormalizedModularJUniformization.cusp.cuspUnit q
  have hproduct := mul_mem_right_sector_of_narrow_right_sectors q u hqre hqsector
    (A.actualPuncturedCuspWitness_cuspUnit_narrow_right_sector q a.2)
  exact two_thirds_lt_inv_re_of_norm_lt_half_of_right_sector
    (q * u) hproduct.1 hproduct.2
    (A.actualPuncturedCuspWitness_cuspProduct_norm_lt_half q a.2)

/-- The entire mapping-torus fibre over the vertex maps into the order-four open. -/
public theorem actualCuspFiberInclusion_mem_orderFourOpen
    {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.totalHomotopyEquiv.invFun
        (finiteBouquetMappingTorusFiberInclusion
          (fun _ : Unit ↦ G.clutching) y) ∈
      R.twoDiscCover.cuspOrderFourOpen := by
  dsimp only
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change G.totalHomotopyEquiv.invFun
      (circleMappingTorusCylinderProjection G.clutching (0, y)) ∈
    R.twoDiscCover.cuspOrderFourOpen
  apply actualCuspCylinder_mem_orderFourOpen_of_rightSector R (0, y)
  · simp
  · simp

/-- The standard mapping-torus vertex cannot map into the order-three side of the actual
affine cover. -/
public theorem not_actualCuspVertexOrderThreePointwiseMembership
    {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ¬ ActualCuspVertexOrderThreePointwiseMembership R := by
  intro h
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let y : G.Fiber := additiveTorusProjection
    (cuspBasePoint A.cuspCoordinate (markedCuspParameter A.starCuspWitness)).1 0
  let p : unitInterval × G.Fiber := (0, y)
  let z : CircleMappingTorus G.clutching :=
    circleMappingTorusCylinderProjection G.clutching p
  have hzvertex : z ∈ vertexPiece (fun _ : Unit ↦ G.clutching) := by
    change finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching) y ∈
      vertexPiece (fun _ : Unit ↦ G.clutching)
    exact fiberInclusion_mem_vertexPiece (fun _ : Unit ↦ G.clutching) y
  have hmem := h z hzvertex
  have hlt := (cuspToEllipticInteriorMap_mem_orderThreeSide_iff_height R _).1 hmem
  have hgt : (2 / 3 : ℝ) <
      A.sectionSevenEllipticCentralHeight
        ⟨R.twoDiscCover.cuspToEllipticInteriorMap (G.totalHomotopyEquiv.invFun z),
          R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage _⟩ := by
    rw [R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus z]
    change (2 / 3 : ℝ) <
      (cuspQ (actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun
        (circleMappingTorusCylinderProjection G.clutching p))).1.2 *
        A.actualNormalizedModularJUniformization.cusp.cuspUnit
          (cuspQ (actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun
            (circleMappingTorusCylinderProjection G.clutching p))).1.2))⁻¹.re
    apply two_thirds_lt_actualCuspCylinderReciprocalProduct_re p
    · simp [p]
    · simp [p]
  linarith

/-- Hence the unswapped oriented refinement proposed for the standard Wang cover is empty. -/
public theorem not_actualCuspOrientedCoverRefinement
    {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ¬ ActualCuspOrientedCoverRefinement R := by
  intro C
  exact not_actualCuspVertexOrderThreePointwiseMembership R
    ((actualCuspOrientedCoverRefinement_iff_pointwiseMembership R).1 C).1

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
