module

public import SphereSixComplex.Topology.PaperSectionSevenCuspAdaptiveSectorBounds
public import SphereSixComplex.Topology.AdaptiveMappingTorusOpenCover
public import SphereSixComplex.Topology.BinaryOpenCoverSwapNaturality

/-!
# Phase comparison for the cusp radial mapping torus

The radial homotopy equivalence forgets only the contractible radial coordinate.  This file
compares its mapping-torus coordinate with the additive cusp parameter modulo integral shifts.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContinuousMap

open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.CuspPeriodExpansion

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

variable {E : Periods.EstablishedFuchsianModularParameter}
  {D : Periods.FuchsianPeriodLocalData E}
  {N : CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate E D}
  {M : StandardInfiniteA2ToricModel.Model}
  {W : ActualPuncturedCuspCollarWitness N M}

namespace UnnormalizedCuspRadialClutchingData

variable (G : UnnormalizedCuspRadialClutchingData W)

/-- The inverse radial homotopy equivalence leaves the mapping-torus coordinate unchanged. -/
public theorem totalHomotopyEquiv_invFun_mappingTorusCoordinate
    (z : let _ := G.fiberTopology; CircleMappingTorus G.clutching) :
    let _ := G.fiberTopology
    (G.totalHomeomorph (G.totalHomotopyEquiv.invFun z)).2 = z := by
  dsimp only
  let _ := G.fiberTopology
  let e : (OpenRadialInterval W.localWitness.radius ×
      CircleMappingTorus G.clutching) ≃ₕ CircleMappingTorus G.clutching :=
    SphereSixComplex.openRadialIntervalProdHomotopyEquiv W.localWitness.radius_pos
  have hinv : G.totalHomotopyEquiv.invFun z =
      G.totalHomeomorph.symm (e.invFun z) := rfl
  rw [hinv, G.totalHomeomorph.apply_symm_apply]
  rfl

end UnnormalizedCuspRadialClutchingData

/-- The two standard presentations of an interval point define the same mapping-torus point. -/
public theorem realMappingTorusHomeomorph_intervalProjection
    {T : Type} [TopologicalSpace T] (phi : T ≃ₜ T) (p : unitInterval × T) :
    realMappingTorusHomeomorph phi (realMappingTorusIntervalProjection phi p) =
      circleMappingTorusCylinderProjection phi p := by
  let C := realMappingTorusClutchingData phi
  let e : CircleMappingTorus phi ≃ RealMappingTorus phi :=
    Equiv.ofBijective C.circleToTotal C.circleToTotal_bijective
  apply e.injective
  change C.circleToTotal
      (C.totalHomeomorphCircleMappingTorus (C.projection p)) =
    C.circleToTotal (circleMappingTorusCylinderProjection phi p)
  rw [show C.circleToTotal
      (C.totalHomeomorphCircleMappingTorus (C.projection p)) = C.projection p by
    exact C.totalHomeomorphCircleMappingTorus.symm_apply_apply _]
  exact C.circleToTotal_mk p

open CuspRadialClutchingConstruction

/-- Equality with an interval representative determines the additive angular coordinate modulo
an integer. -/
public theorem realMappingTorusChart_eq_intervalProjection_exists_int
    (x : Periods.PeriodDomain) (s : ℂ) (v : ComplexTorus.ComplexTwoSpace)
    (p : unitInterval × AdditiveTorus x.1)
    (h : realMappingTorusChart x (s.re, v) =
      realMappingTorusIntervalProjection (cuspFiberClutching x) p) :
    ∃ k : ℤ, s.re = (p.1 : ℝ) + k := by
  change Quotient.mk (realMappingTorusSetoid (cuspFiberClutching x))
      (s.re, additiveTorusProjection x.1 v) =
    Quotient.mk (realMappingTorusSetoid (cuspFiberClutching x)) ((p.1 : ℝ), p.2) at h
  obtain ⟨k, hk⟩ := (realMappingTorusMk_eq_iff _ _ _).mp h
  refine ⟨k, ?_⟩
  have hre := congrArg Prod.fst hk
  change (p.1 : ℝ) = s.re - k at hre
  linarith

/-- An additive representative of a radial mapping-torus cylinder point has the same angular
coordinate modulo an integer. -/
public theorem additiveCuspLift_re_eq_cylinder_mod_int
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData W
      let _ := G.fiberTopology
      unitInterval × G.Fiber)
    (a : additiveCuspRadiusCover W.localWitness.radius)
    (ha : let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData W
      let _ := G.fiberTopology
      collarPeriodPointMap W a = G.totalHomotopyEquiv.invFun
        (circleMappingTorusCylinderProjection G.clutching p)) :
    ∃ k : ℤ, a.1.2.re = (p.1 : ℝ) + k := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData W
  let _ := G.fiberTopology
  let z := circleMappingTorusCylinderProjection G.clutching p
  have hcoord : (G.totalHomeomorph (G.totalHomotopyEquiv.invFun z)).2 = z :=
    G.totalHomotopyEquiv_invFun_mappingTorusCoordinate z
  have happ := puncturedLocalCuspQuotientHomeomorph_apply W (markedCuspParameter W) a
  have hsecond : realMappingTorusHomeomorph G.clutching
      (collarRadialMap W (markedCuspParameter W) a).2 = z := by
    calc
      realMappingTorusHomeomorph G.clutching
          (collarRadialMap W (markedCuspParameter W) a).2 =
          (G.totalHomeomorph (collarPeriodPointMap W a)).2 :=
        (congrArg Prod.snd happ).symm
      _ = (G.totalHomeomorph (G.totalHomotopyEquiv.invFun z)).2 :=
        congrArg (fun q ↦ (G.totalHomeomorph q).2) ha
      _ = z := hcoord
  have hinterval := realMappingTorusHomeomorph_intervalProjection G.clutching p
  have hreal : (collarRadialMap W (markedCuspParameter W) a).2 =
      realMappingTorusIntervalProjection G.clutching p :=
    (realMappingTorusHomeomorph G.clutching).injective (hsecond.trans hinterval.symm)
  apply realMappingTorusChart_eq_intervalProjection_exists_int
    (cuspBasePoint N (markedCuspParameter W)) a.1.2
    (collarFiberEquiv N (markedCuspParameter W) a.1.2 a.1.1) p
  exact hreal

/-- The cusp exponential depends only on the additive angular coordinate modulo integers. -/
public theorem cuspQ_eq_polar_of_re_eq_mod_int
    (s : ℂ) (t : ℝ) (k : ℤ) (h : s.re = t + k) :
    cuspQ s = cuspQ (cuspParameterOfPolar ‖cuspQ s‖ t) := by
  have hpolar : cuspParameterOfPolar ‖cuspQ s‖ s.re =
      cuspParameterOfPolar ‖cuspQ s‖ t + (k : ℂ) := by
    apply Complex.ext
    · simpa [cuspParameterOfPolar] using h
    · simp [cuspParameterOfPolar]
  calc
    cuspQ s = cuspQ (cuspParameterOfPolar ‖cuspQ s‖ s.re) :=
      congrArg cuspQ (cuspParameterOfPolar_norm_cuspQ s).symm
    _ = cuspQ (cuspParameterOfPolar ‖cuspQ s‖ t + (k : ℂ)) :=
      congrArg cuspQ hpolar
    _ = cuspQ (cuspParameterOfPolar ‖cuspQ s‖ t) := cuspQ_add_int _ k

/-- Real part of the cusp exponential in polar coordinates. -/
public theorem cuspQ_cuspParameterOfPolar_re
    (rho t : ℝ) (hrho : 0 < rho) :
    (cuspQ (cuspParameterOfPolar rho t)).re =
      rho * Real.cos (2 * Real.pi * t) := by
  rw [cuspQ, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, cuspParameterOfPolar, mul_zero, sub_zero,
    mul_one, add_zero]
  norm_num
  have harg : -(2 * Real.pi * (-Real.log rho / (2 * Real.pi))) =
      Real.log rho := by field_simp
  rw [harg, Real.exp_log hrho]
  exact Or.inl rfl

/-- Imaginary part of the cusp exponential in polar coordinates. -/
public theorem cuspQ_cuspParameterOfPolar_im
    (rho t : ℝ) (hrho : 0 < rho) :
    (cuspQ (cuspParameterOfPolar rho t)).im =
      rho * Real.sin (2 * Real.pi * t) := by
  rw [cuspQ, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, cuspParameterOfPolar, mul_zero, sub_zero,
    mul_one, add_zero]
  norm_num
  have harg : -(2 * Real.pi * (-Real.log rho / (2 * Real.pi))) =
      Real.log rho := by field_simp
  rw [harg, Real.exp_log hrho]
  exact Or.inl rfl

/-- The cusp exponential of an additive lift of a cylinder point is the polar point at the
cylinder coordinate, with the lift's radial modulus. -/
public theorem additiveCuspLift_cuspQ_eq_cylinderPolar
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData W
      let _ := G.fiberTopology
      unitInterval × G.Fiber)
    (a : additiveCuspRadiusCover W.localWitness.radius)
    (ha : let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData W
      let _ := G.fiberTopology
      collarPeriodPointMap W a = G.totalHomotopyEquiv.invFun
        (circleMappingTorusCylinderProjection G.clutching p)) :
    cuspQ a.1.2 = cuspQ (cuspParameterOfPolar ‖cuspQ a.1.2‖ (p.1 : ℝ)) := by
  obtain ⟨k, hk⟩ := additiveCuspLift_re_eq_cylinder_mod_int W p a ha
  exact cuspQ_eq_polar_of_re_eq_mod_int a.1.2 p.1 k hk

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

namespace SphereSixComplex.Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction
open CuspPeriodExpansion
open CategoryTheory TopologicalSpace

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The pulled-back affine cusp cover in the corrected order: order four first, order three
second. -/
public theorem actualCuspMappingTorusPulledBackSwappedOpenCover
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspMappingTorusOrderFourOpen R ⊔
      actualCuspMappingTorusOrderThreeOpen R = ⊤ := by
  rw [sup_comm]
  exact actualCuspMappingTorusPulledBackOpenCover R

/-- Canonical Mayer--Vietoris comparison for the pulled-back cusp cover in corrected order. -/
public noncomputable def actualCuspMappingTorusPulledBackSwappedHomologyComparison
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    SphereSixComplex.BinaryOpenCover.OpenCoverHomologyComparison
      (actualCuspMappingTorusOrderFourOpen R)
      (actualCuspMappingTorusOrderThreeOpen R) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover
    (actualCuspMappingTorusPulledBackSwappedOpenCover R)

/-- Reversing the pulled-back cusp cover negates its ordinary Mayer--Vietoris boundary. -/
public theorem actualCuspMappingTorusPulledBack_boundary_swap
    (R : A.SectionSevenAffineRadialCompletionInput) (n : ℕ) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (actualCuspMappingTorusPulledBackHomologyComparison R).boundary n ≫
        SphereSixComplex.BinaryOpenCover.openIntersectionSwapHomologyMap
          (actualCuspMappingTorusOrderThreeOpen R)
          (actualCuspMappingTorusOrderFourOpen R) n =
      -(actualCuspMappingTorusPulledBackSwappedHomologyComparison R).boundary n := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact SphereSixComplex.BinaryOpenCover.openCoverHomologyComparisonOfCover_boundary_swap
    (actualCuspMappingTorusPulledBackOpenCover R)
    (actualCuspMappingTorusPulledBackSwappedOpenCover R) n

/-- The selected additive lift used by the affine-height formula has the cylinder point's cusp
phase, independently of the selected integral representative. -/
public theorem actualCuspAdditiveLift_cuspQ_eq_cylinderPolar
    (p : let G := (CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness)
      let _ := G.fiberTopology
      unitInterval × G.Fiber) :
    let G := (CuspRadialClutchingConstruction.actualCuspRadialClutchingData
      A.starCuspWitness)
    let _ := G.fiberTopology
    let z := circleMappingTorusCylinderProjection G.clutching p
    let a := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
    cuspQ a.1.2 = cuspQ (cuspParameterOfPolar ‖cuspQ a.1.2‖ (p.1 : ℝ)) := by
  dsimp only
  let _ := (CuspRadialClutchingConstruction.actualCuspRadialClutchingData
    A.starCuspWitness).fiberTopology
  apply additiveCuspLift_cuspQ_eq_cylinderPolar A.starCuspWitness p
    (actualCuspAdditiveLift
      ((CuspRadialClutchingConstruction.actualCuspRadialClutchingData
        A.starCuspWitness).totalHomotopyEquiv.invFun
        (circleMappingTorusCylinderProjection
          (CuspRadialClutchingConstruction.actualCuspRadialClutchingData
            A.starCuspWitness).clutching p)))
  exact additiveCuspBoundaryProjection_actualCuspAdditiveLift _

/-- The same phase bridge stated directly for the paper's selected radial clutching datum. -/
public theorem actualCuspAdditiveLift_cuspQ_eq_mappingTorusCylinderPolar
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    let z := circleMappingTorusCylinderProjection G.clutching p
    let a := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
    cuspQ a.1.2 = cuspQ (cuspParameterOfPolar ‖cuspQ a.1.2‖ (p.1 : ℝ)) := by
  exact actualCuspAdditiveLift_cuspQ_eq_cylinderPolar (A := A) p

/-- Exact cosine formula for the cusp parameter selected above a mapping-torus cylinder point. -/
public theorem actualCuspAdditiveLift_cuspQ_re_eq_mappingTorusCos
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    let z := circleMappingTorusCylinderProjection G.clutching p
    let a := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
    (cuspQ a.1.2).re = ‖cuspQ a.1.2‖ * Real.cos (2 * Real.pi * (p.1 : ℝ)) := by
  dsimp only
  have heq := actualCuspAdditiveLift_cuspQ_eq_mappingTorusCylinderPolar (A := A) p
  exact (congrArg Complex.re heq).trans
    (cuspQ_cuspParameterOfPolar_re _ _ (norm_cuspQ_pos _))

/-- Exact sine formula for the cusp parameter selected above a mapping-torus cylinder point. -/
public theorem actualCuspAdditiveLift_cuspQ_im_eq_mappingTorusSin
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    let z := circleMappingTorusCylinderProjection G.clutching p
    let a := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
    (cuspQ a.1.2).im = ‖cuspQ a.1.2‖ * Real.sin (2 * Real.pi * (p.1 : ℝ)) := by
  dsimp only
  have heq := actualCuspAdditiveLift_cuspQ_eq_mappingTorusCylinderPolar (A := A) p
  exact (congrArg Complex.im heq).trans
    (cuspQ_cuspParameterOfPolar_im _ _ (norm_cuspQ_pos _))

/-- A cylinder phase in the narrowed right sector lies on the order-four side of the affine
height cover. -/
public theorem one_third_lt_actualCuspCylinderReciprocalProduct_re
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
    (1 / 3 : ℝ) <
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
  exact one_third_lt_actualCuspReciprocalProduct_re q a.2 hqre hqsector

/-- A cylinder phase in the left-facing sector lies on the order-three side of the affine
height cover. -/
public theorem actualCuspCylinderReciprocalProduct_re_lt_two_thirds
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber)
    (hcos : Real.cos (2 * Real.pi * (p.1 : ℝ)) < 0)
    (hsector : |Real.sin (2 * Real.pi * (p.1 : ℝ))| ≤
      -Real.cos (2 * Real.pi * (p.1 : ℝ))) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    let z := circleMappingTorusCylinderProjection G.clutching p
    let a := actualCuspAdditiveLift (G.totalHomotopyEquiv.invFun z)
    (cuspQ a.1.2 * A.actualNormalizedModularJUniformization.cusp.cuspUnit
      (cuspQ a.1.2))⁻¹.re < (2 / 3 : ℝ) := by
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
  have hqsector : |q.im| ≤ -q.re := by
    change |(cuspQ a.1.2).im| ≤ -(cuspQ a.1.2).re
    rw [hre, him, abs_mul, abs_of_pos hrho]
    nlinarith [mul_nonneg hrho.le
      (abs_nonneg (Real.sin (2 * Real.pi * (p.1 : ℝ))))]
  exact actualCuspReciprocalProduct_re_lt_two_thirds q a.2 hqre hqsector

/-- The right-sector cylinder band maps into the pulled-back order-four open. -/
public theorem actualCuspCylinder_mem_orderFourOpen_of_rightSector
    (R : A.SectionSevenAffineRadialCompletionInput)
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber)
    (hcos : 0 < Real.cos (2 * Real.pi * (p.1 : ℝ)))
    (hsector : 50 * |Real.sin (2 * Real.pi * (p.1 : ℝ))| ≤
      49 * Real.cos (2 * Real.pi * (p.1 : ℝ))) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.totalHomotopyEquiv.invFun
      (circleMappingTorusCylinderProjection G.clutching p) ∈
        R.twoDiscCover.cuspOrderFourOpen := by
  dsimp only
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let z := circleMappingTorusCylinderProjection G.clutching p
  let q := G.totalHomotopyEquiv.invFun z
  change R.twoDiscCover.cuspToEllipticInteriorMap q ∈ R.twoDiscCover.orderFourSide
  apply (cuspToEllipticInteriorMap_mem_orderFourSide_iff_height R q).2
  rw [R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus z]
  exact one_third_lt_actualCuspCylinderReciprocalProduct_re p hcos hsector

/-- The left-sector cylinder band maps into the pulled-back order-three open. -/
public theorem actualCuspCylinder_mem_orderThreeOpen_of_leftSector
    (R : A.SectionSevenAffineRadialCompletionInput)
    (p : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      unitInterval × G.Fiber)
    (hcos : Real.cos (2 * Real.pi * (p.1 : ℝ)) < 0)
    (hsector : |Real.sin (2 * Real.pi * (p.1 : ℝ))| ≤
      -Real.cos (2 * Real.pi * (p.1 : ℝ))) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.totalHomotopyEquiv.invFun
      (circleMappingTorusCylinderProjection G.clutching p) ∈
        R.twoDiscCover.cuspOrderThreeOpen := by
  dsimp only
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let z := circleMappingTorusCylinderProjection G.clutching p
  let q := G.totalHomotopyEquiv.invFun z
  change R.twoDiscCover.cuspToEllipticInteriorMap q ∈ R.twoDiscCover.orderThreeSide
  apply (cuspToEllipticInteriorMap_mem_orderThreeSide_iff_height R q).2
  rw [R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus z]
  exact actualCuspCylinderReciprocalProduct_re_lt_two_thirds p hcos hsector

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
