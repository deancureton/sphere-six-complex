module

public import SphereSixComplex.Topology.IdentityUnitMappingTorusLowOverlapCoordinate

/-!
# The identity point-mapping-torus Wang boundary

The degree-zero Wang boundary for the identity mapping torus of a point is an additive
equivalence with the integers.  Consequently, agreement of winding and Wang coordinates on its
boundary-positive generator implies agreement on every first-homology class.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex.Topology.IdentityPointMappingTorusWindingBoundary

open SphereSixComplex.MappingTorusBaseCircleWangBoundaryNaturality
open SphereSixComplex.MappingTorusBaseCircleWangNaturality
open SphereSixComplex.BinaryOpenCover
open SphereSixComplex.MappingTorusDegreeOneCoverComparison
open SphereSixComplex.StandardCircleHomologyLiftDegree
open SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality
open SphereSixComplex.Topology.IdentityUnitMappingTorusPositiveBoundary
open SphereSixComplex.Topology.IdentityUnitMappingTorusLowOverlapCoordinate

/-- The integer-valued degree-zero Wang boundary for the identity mapping torus of a point. -/
public def identityPointMappingTorusWangBoundaryInt :
    IntegralSingularHomology 1
        (CircleMappingTorus (Homeomorph.refl Unit)) →+ ℤ :=
  (pathConnectedIntegralHomologyZeroEquivInteger Unit).toAddMonoidHom.comp
    (circleMappingTorusWangPresentationOfCover
      (Homeomorph.refl Unit) 0).boundary

/-- The point-fibre degree-zero Wang boundary is bijective. -/
public theorem identityPointMappingTorusWangBoundaryInt_bijective :
    Function.Bijective identityPointMappingTorusWangBoundaryInt := by
  let P := circleMappingTorusWangPresentationOfCover (Homeomorph.refl Unit) 0
  have : Subsingleton (IntegralSingularHomology 1 Unit) :=
    AddCommGrpCat.subsingleton_of_isZero
      (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (C := AddCommGrpCat) (n := 1) (AddCommGrpCat.of ℤ) (TopCat.of Unit) one_ne_zero)
  have hinj : Function.Injective P.boundary := by
    intro x y hxy
    have hz : P.boundary (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨a, ha⟩ := (P.exact_inclusion_boundary (x - y)).mp hz
    have ha0 : a = 0 := Subsingleton.elim _ _
    rw [ha0, map_zero] at ha
    exact sub_eq_zero.mp ha.symm
  have hsurj : Function.Surjective P.boundary := by
    intro y
    apply (P.exact_boundary_lowDifference y).mp
    change integralSingularHomologyMap 0
        ((Homeomorph.refl Unit : Unit ≃ₜ Unit) : C(Unit, Unit)) y - y = 0
    rw [show ((Homeomorph.refl Unit : Unit ≃ₜ Unit) : C(Unit, Unit)) =
        ContinuousMap.id Unit by rfl, integralSingularHomologyMap_id_wang, sub_self]
  exact
    ⟨(pathConnectedIntegralHomologyZeroEquivInteger Unit).injective.comp hinj,
      (pathConnectedIntegralHomologyZeroEquivInteger Unit).surjective.comp hsurj⟩

/-- The canonical Wang-boundary coordinate on the identity point mapping torus. -/
public def identityPointMappingTorusWangBoundaryEquiv :
    IntegralSingularHomology 1
        (CircleMappingTorus (Homeomorph.refl Unit)) ≃+ ℤ :=
  AddEquiv.ofBijective identityPointMappingTorusWangBoundaryInt
    identityPointMappingTorusWangBoundaryInt_bijective

/-- The class whose canonical degree-zero Wang boundary is `+1`. -/
public def identityPointMappingTorusPositiveGenerator :
    IntegralSingularHomology 1
        (CircleMappingTorus (Homeomorph.refl Unit)) :=
  identityPointMappingTorusWangBoundaryEquiv.symm 1

public theorem identityPointMappingTorusPositiveGenerator_wangBoundary :
    identityPointMappingTorusWangBoundaryEquiv
      identityPointMappingTorusPositiveGenerator = 1 :=
  identityPointMappingTorusWangBoundaryEquiv.apply_symm_apply 1

/-- A positive winding calibration on the boundary-positive generator determines the full
identity-point winding/Wang comparison. -/
public theorem identityPointMappingTorus_winding_eq_wangBoundary_of_positive
    (hpositive :
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
          (integralSingularHomologyMap 1
            (circleMappingTorusBaseCircleProjection (Homeomorph.refl Unit))
            identityPointMappingTorusPositiveGenerator) = 1)
    (z : IntegralSingularHomology 1
      (CircleMappingTorus (Homeomorph.refl Unit))) :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (circleMappingTorusBaseCircleProjection (Homeomorph.refl Unit)) z) =
      pathConnectedIntegralHomologyZeroEquivInteger Unit
        ((circleMappingTorusWangPresentationOfCover
          (Homeomorph.refl Unit) 0).boundary z) := by
  let e := identityPointMappingTorusWangBoundaryEquiv
  let w : IntegralSingularHomology 1
        (CircleMappingTorus (Homeomorph.refl Unit)) →+ ℤ :=
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding.comp
      (integralSingularHomologyMap 1
        (circleMappingTorusBaseCircleProjection (Homeomorph.refl Unit)))
  change w identityPointMappingTorusPositiveGenerator = 1 at hpositive
  change w z = e z
  have hz : z = e z • identityPointMappingTorusPositiveGenerator := by
    apply e.injective
    rw [map_zsmul, identityPointMappingTorusPositiveGenerator_wangBoundary]
    simp
  calc
    w z = w (e z • identityPointMappingTorusPositiveGenerator) := congrArg w hz
    _ = e z • w identityPointMappingTorusPositiveGenerator := map_zsmul w (e z) _
    _ = e z := by rw [hpositive]; simp

/-- The point calibration transports to every path-connected circle mapping torus. -/
public theorem circleMappingTorusBaseCircle_winding_eq_wangBoundary_of_positive
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F]
    (hpositive :
      StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
          (integralSingularHomologyMap 1
            (circleMappingTorusBaseCircleProjection (Homeomorph.refl Unit))
            identityPointMappingTorusPositiveGenerator) = 1)
    (phi : F ≃ₜ F)
    (z : IntegralSingularHomology 1 (CircleMappingTorus phi)) :
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (circleMappingTorusBaseCircleProjection phi) z) =
      pathConnectedIntegralHomologyZeroEquivInteger F
        ((circleMappingTorusWangPresentationOfCover phi 0).boundary z) := by
  rw [← pointMappingTorusProjection_baseCircle phi,
    ← integralSingularHomologyMap_comp_wang,
    identityPointMappingTorus_winding_eq_wangBoundary_of_positive hpositive,
    pointMappingTorusProjection_wangBoundary_naturality,
    pathConnectedIntegralHomologyZeroEquivInteger_naturality]

/-- The positive cylinder has canonical Wang boundary coordinate `+1`. -/
public theorem positiveCylinderClass_wangBoundary :
    identityPointMappingTorusWangBoundaryEquiv positiveCylinderClass = 1 := by
  change identityPointMappingTorusWangBoundaryInt positiveCylinderClass = 1
  change pathConnectedIntegralHomologyZeroEquivInteger PointFiber
      ((circleMappingTorusWangPresentationOfCover
        (Homeomorph.refl PointFiber) 0).boundary positiveCylinderClass) = 1
  have hwang := DFunLike.congr_fun
    (lowOverlapRead_comp_boundary (Homeomorph.refl PointFiber) 0)
    positiveCylinderClass
  change lowOverlapRead (Homeomorph.refl PointFiber) 0
      ((mappingTorusOpenCoverHomologyComparison
        (Homeomorph.refl PointFiber)).boundaryHom 0 positiveCylinderClass) =
    (circleMappingTorusWangPresentationOfCover
      (Homeomorph.refl PointFiber) 0).boundary positiveCylinderClass at hwang
  rw [← hwang, ← positiveBoundaryCalibration_union]
  change pathConnectedIntegralHomologyZeroEquivInteger PointFiber
      (lowOverlapRead (Homeomorph.refl PointFiber) 0
        (ConcreteCategory.hom
          ((mappingTorusOpenCoverHomologyComparison
            (Homeomorph.refl PointFiber)).boundary 0)
          (ConcreteCategory.hom
            ((mappingTorusOpenCoverHomologyComparison
              (Homeomorph.refl PointFiber)).unionIso 1).hom
            positiveBoundaryCalibration.source))) = 1
  rw [← ConcreteCategory.comp_apply,
    OpenCoverHomologyComparison.unionIso_hom_comp_boundary]
  simp only [ConcreteCategory.comp_apply]
  rw [positiveBoundaryCalibration_ordinary]
  exact positiveBoundaryCalibration_lowOverlapRead_integer

/-- The geometric positive cylinder is the boundary-positive generator. -/
public theorem positiveCylinderClass_eq_positiveGenerator :
    positiveCylinderClass = identityPointMappingTorusPositiveGenerator := by
  apply identityPointMappingTorusWangBoundaryEquiv.injective
  rw [positiveCylinderClass_wangBoundary,
    identityPointMappingTorusPositiveGenerator_wangBoundary]

/-- The boundary-positive generator has positive base-circle winding. -/
public theorem identityPointMappingTorusPositiveGenerator_baseCircle_winding :
    unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (circleMappingTorusBaseCircleProjection (Homeomorph.refl Unit))
          identityPointMappingTorusPositiveGenerator) = 1 := by
  rw [← positiveCylinderClass_eq_positiveGenerator]
  exact positiveCylinderClass_baseCircle_winding

/-- Winding equals the canonical Wang coordinate on the point mapping torus. -/
public theorem identityPointMappingTorus_winding_eq_wangBoundary
    (z : IntegralSingularHomology 1
      (CircleMappingTorus (Homeomorph.refl Unit))) :
    unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (circleMappingTorusBaseCircleProjection (Homeomorph.refl Unit)) z) =
      pathConnectedIntegralHomologyZeroEquivInteger Unit
        ((circleMappingTorusWangPresentationOfCover
          (Homeomorph.refl Unit) 0).boundary z) :=
  identityPointMappingTorus_winding_eq_wangBoundary_of_positive
    identityPointMappingTorusPositiveGenerator_baseCircle_winding z

/-- Base-circle winding equals the canonical Wang coordinate for every path-connected fibre. -/
public theorem circleMappingTorusBaseCircle_winding_eq_wangBoundary
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F]
    (phi : F ≃ₜ F)
    (z : IntegralSingularHomology 1 (CircleMappingTorus phi)) :
    unitCircleHomologyWinding
        (integralSingularHomologyMap 1
          (circleMappingTorusBaseCircleProjection phi) z) =
      pathConnectedIntegralHomologyZeroEquivInteger F
        ((circleMappingTorusWangPresentationOfCover phi 0).boundary z) :=
  circleMappingTorusBaseCircle_winding_eq_wangBoundary_of_positive
    identityPointMappingTorusPositiveGenerator_baseCircle_winding phi z

end SphereSixComplex.Topology.IdentityPointMappingTorusWindingBoundary

end

end
