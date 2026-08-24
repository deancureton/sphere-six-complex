module

public import SphereSixComplex.Geometry.RegularTorusFamily
public import SphereSixComplex.Periods.FuchsianUniformizationBridge
public import SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-!
# The regular torus family over the explicit Fuchsian source

The arithmetic termination theorem supplies the proper-discontinuity hypothesis in the regular
torus-family construction when the source action is the explicit triangle-group action.
-/

open scoped Manifold

namespace SphereSixComplex.Geometry.GlobalTorusFamily

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.TorusFamily SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

public noncomputable section

/-- The punctured family built from an explicit Fuchsian modular parameter is a complex manifold,
and its deck-quotient projection is locally biholomorphic. -/
public theorem fuchsianPuncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph
    (P : FuchsianModularParameter)
    (F : PeriodFunctions P.toTriangleUniformization) :
    let hproper : SourceActionProperlyDiscontinuous :=
      sourceActionProperlyDiscontinuous_of_eq P.toTriangleUniformization_sourceAction
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace (RegularBase (U := P.toTriangleUniformization)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
        (RegularBase (U := P.toTriangleUniformization)) :=
      regularBase_isManifold hproper
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a ↦ (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
        (regularParameterMap_compactUniformLowerBound F))
    letI : LocallyCompactSpace (RegularTotalSpace F) :=
      Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
    letI := regularFamilyDeckAction F
    letI := regularFamilyDeckAction_isCancelSMul_of_fuchsian F
      P.toTriangleUniformization_sourceAction hproper
    letI := regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
    letI := regularFamilyDeckAction_continuousConstSMul F hproper
    IsManifold GlobalDeckTotalModel RegularSmoothnessOrder (PuncturedGlobalFamily F) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (quotientProjection (M := RegularTotalSpace F) (G := Delta)) := by
  exact puncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph F
    P.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq P.toTriangleUniformization_sourceAction)

end

end SphereSixComplex.Geometry.GlobalTorusFamily
