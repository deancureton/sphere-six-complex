module

public import SphereSixComplex.Geometry.FuchsianRegularTorusFamily
public import SphereSixComplex.Geometry.PaperCentralFamilyTopology
public import SphereSixComplex.Topology.ManifoldLocallyContractible

/-!
# Local niceness of the punctured global family

The punctured global family of a Fuchsian modular parameter is a complex manifold
(`fuchsianPuncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph`), so its local
point-set properties are read off its charts rather than assumed.

`fuchsianPuncturedGlobalFamilyProductCharts` records the product-model charted structure for an
arbitrary Fuchsian modular parameter.  Over that model the family is strongly locally contractible,
hence locally path connected and semilocally simply connected — the two hypotheses Tau Ceti's
based-path universal cover needs of a base space.

Path connectedness follows too: the family is connected for any triangle uniformization
(`puncturedGlobalFamily_connected`), and a connected, locally path connected space is path
connected.
-/

@[expose] public section

noncomputable section

open scoped Manifold

namespace SphereSixComplex.Geometry.GlobalTorusFamily

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (P : FuchsianModularParameter) (F : PeriodFunctions P.toTriangleUniformization)

/-- Product-model charts on the punctured global family of a Fuchsian modular parameter. -/
@[instance_reducible] public noncomputable def fuchsianPuncturedGlobalFamilyProductCharts :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (PuncturedGlobalFamily F) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq P.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace (RegularBase (U := P.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := P.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a => (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
      (regularParameterMap_compactUniformLowerBound F))
  let htotal := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    F hproper RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder (RegularTotalSpace F) := htotal.1
  let _ : LocallyCompactSpace (RegularTotalSpace F) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction F
  let _ : IsCancelSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian F
      P.toTriangleUniformization_sourceAction hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  infer_instance

/-- The punctured global family is strongly locally contractible: each chart identifies a
neighbourhood with an open subset of `ℂ × ℂ²`, whose balls are convex. -/
public theorem fuchsianPuncturedGlobalFamily_stronglyLocallyContractible :
    StronglyLocallyContractibleSpace (PuncturedGlobalFamily F) := by
  let _ := fuchsianPuncturedGlobalFamilyProductCharts P F
  have _ : StronglyLocallyContractibleSpace (ModelProd ℂ ComplexTwoSpace) :=
    normedSpace_stronglyLocallyContractibleSpace (E := ℂ × ComplexTwoSpace)
  exact ChartedSpace.stronglyLocallyContractibleSpace (H := ModelProd ℂ ComplexTwoSpace)

/-- The punctured global family is locally path connected. -/
public theorem fuchsianPuncturedGlobalFamily_locallyPathConnected :
    LocallyPathConnectedSpace (PuncturedGlobalFamily F) := by
  have _ : StronglyLocallyContractibleSpace (PuncturedGlobalFamily F) :=
    fuchsianPuncturedGlobalFamily_stronglyLocallyContractible P F
  infer_instance

/-- The punctured global family is path connected: it is connected, and locally path connected
because it is a manifold. -/
public theorem fuchsianPuncturedGlobalFamily_pathConnected :
    PathConnectedSpace (PuncturedGlobalFamily F) := by
  have _ : LocallyPathConnectedSpace (PuncturedGlobalFamily F) :=
    fuchsianPuncturedGlobalFamily_locallyPathConnected P F
  have _ : ConnectedSpace (PuncturedGlobalFamily F) := puncturedGlobalFamily_connected F
  exact pathConnectedSpace_iff_connectedSpace.mpr inferInstance

/-- The punctured global family is semilocally simply connected. -/
public theorem fuchsianPuncturedGlobalFamily_semilocallySimplyConnected :
    TauCeti.SemilocallySimplyConnectedSpace (PuncturedGlobalFamily F) := by
  let _ := fuchsianPuncturedGlobalFamilyProductCharts P F
  have _ : StronglyLocallyContractibleSpace (ModelProd ℂ ComplexTwoSpace) :=
    normedSpace_stronglyLocallyContractibleSpace (E := ℂ × ComplexTwoSpace)
  exact ChartedSpace.semilocallySimplyConnectedSpace (H := ModelProd ℂ ComplexTwoSpace)

end SphereSixComplex.Geometry.GlobalTorusFamily

end

end
