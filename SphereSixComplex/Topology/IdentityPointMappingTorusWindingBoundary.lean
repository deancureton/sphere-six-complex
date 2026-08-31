module

public import SphereSixComplex.Topology.MappingTorusBaseCircleWangBoundaryNaturality

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

end SphereSixComplex.Topology.IdentityPointMappingTorusWindingBoundary

end

end
