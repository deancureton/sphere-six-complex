module

public import SphereSixComplex.Geometry.PaperCentralFamilyTopology
public import SphereSixComplex.Geometry.PaperOpenEmbeddingStar

/-!
# Hausdorffness of the four concrete star pieces

The central family and three filling pieces are orbit quotients of Hausdorff, locally compact
spaces by free properly discontinuous actions.  This module installs those action data locally
and records the resulting Hausdorff conclusions in the star's dependent indexing.
-/

open scoped Manifold ContDiff

namespace SphereSixComplex.Geometry

open Set Topology SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open TorusFamily AnalyticTorusFamily GlobalTorusFamily ComplexTorus
open EllipticVaryingFamilyQuotient
open CuspPuncturedCollarBridge CuspPhaseEstimates CuspPeriodExpansion
open CuspFilling CuspLocalPhaseAction StandardInfiniteA2ToricModel

noncomputable section

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The regular central family quotient is Hausdorff. -/
public theorem centralFamily_t2 : T2Space A.CentralFamily := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap A.periods)
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    fun a ↦ (regularPeriodSection_contMDiff A.periods hproper a
      RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
  let _ : LocallyCompactSpace (RegularTotalSpace A.periods) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction A.periods
  let _ : IsCancelSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source A.periods hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_continuousConstSMul A.periods hproper
  infer_instance

/-- The actual phase-corrected local cusp filling quotient is Hausdorff. -/
public theorem actualLocalCuspFilling_t2
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    T2Space (actualLocalCuspFilling W) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let _ : LocallyCompactSpace M.Carrier :=
    ChartedSpace.locallyCompactSpace ComplexModel M.Carrier
  let _ : LocallyCompactSpace (LocalCarrier M W.localWitness.radius) :=
    (cuspNeighborhood M W.localWitness.radius).isOpen.locallyCompactSpace
  let _ : IsCancelSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).action_free
  let _ : ProperlyDiscontinuousSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    C.properlyDiscontinuous W.localWitness.fixedPoint W.localWitness.compactOverlap
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) := by
    constructor
    intro gamma
    convert (C.genericPsiMap_holomorphic W.localWitness.fixedPoint
      (Multiplicative.toAdd gamma)).continuous using 1
    funext p
    exact (C.toCuspActionData W.localWitness.fixedPoint).psi_smul
      (Multiplicative.toAdd gamma) p
  infer_instance

/-- The order-three varying filling quotient is Hausdorff. -/
public theorem orderThreeFilling_t2 (r : ℝ) :
    T2Space (A.OrderThreeVaryingFilling r) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingOpen r) := A.orderThreeFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderThreeFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderThreeFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) := by
    infer_instance
  infer_instance

/-- The order-four varying filling quotient is Hausdorff. -/
public theorem orderFourFilling_t2 (r : ℝ) :
    T2Space (A.OrderFourVaryingFilling r) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingOpen r) := A.orderFourFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderFourFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderFourFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) := by
    infer_instance
  infer_instance

/-- Each of the three concrete filling pieces is Hausdorff. -/
public theorem starFilling_t2 (i : Fin 3) : T2Space (A.starFillingType i) := by
  fin_cases i
  · exact actualLocalCuspFilling_t2 A.starCuspWitness
  · exact A.orderThreeFilling_t2 A.starSeparation.orderThree.radius
  · exact A.orderFourFilling_t2 A.starSeparation.orderFour.radius

/-- Every piece of the concrete four-piece star is Hausdorff. -/
public theorem starPiece_t2 (i : Option (Fin 3)) :
    T2Space (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.U i) := by
  cases i with
  | none => exact A.centralFamily_t2
  | some i => exact A.starFilling_t2 i

end PaperAnalyticData

end

end SphereSixComplex.Geometry
