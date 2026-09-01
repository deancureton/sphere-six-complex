module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourProjectedFactorizationProof
public import SphereSixComplex.Topology.PaperActualEllipticOrderFourGeometricRelatorRepresentativeProof

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open SphereSixComplex.Geometry
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The restricted order-four product chart followed by projection to the central family. -/
public noncomputable def orderFourPuncturedProductCentralRealizationMap :
    letI := A.orderFourActualEllipticBoundaryAction
    C(A.OrderFourCayleyPuncturedDisc × A.orderFourTorus, A.CentralFamily) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact
    { toFun := fun zq ↦ A.centralQuotientProjection
        (A.orderFourPuncturedProductRegularRealizationMap zq)
      continuous_toFun := A.centralQuotientProjection_isLocalHomeomorph.continuous.comp
        A.orderFourPuncturedProductRegularRealizationMap.continuous }

/-- The fixed-base fibre factor supplied by the restricted product splitting. -/
public noncomputable def orderFourCentralFiberFactor :
    letI := A.orderFourActualEllipticBoundaryAction
    Path A.orderFourActualEllipticCentralBase A.orderFourActualEllipticCentralBase := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let x := A.orderFourCayleyPuncturedBasepoint
  let q := A.orderFourPrincipalGaugeWithOffsetPath
  let y := A.orderFourFillingRelationPrincipalGaugeLoop 0 +
    Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2
  let f := A.orderFourPuncturedProductCentralRealizationMap
  let raw := ((Path.refl x).prod q).map f.continuous
  have hregular : A.orderFourCollarRegularRepresentativeMap
      A.orderFourActualEllipticBoundaryBase =
        A.orderFourPuncturedProductRegularRealizationMap (x, y) := by
    exact A.orderFourFillingRelationRegularLoop.source.symm |>.trans
      ((A.orderFourRegularLoop_eq_puncturedProductRealization 0).symm.trans
        (congrArg A.orderFourPuncturedProductRegularRealizationMap
          (Prod.ext A.orderFourFillingRelationCayleyPuncturedLoop.source
            A.orderFourPrincipalGaugeWithOffsetPath.source)))
  have hbase : A.orderFourActualEllipticCentralBase = f (x, y) := by
    exact A.orderFourCollarRegularRepresentative_base_projects.symm.trans
      (congrArg A.centralQuotientProjection hregular)
  exact raw.cast hbase hbase

/-- The fixed-fibre base factor supplied by the restricted product splitting. -/
public noncomputable def orderFourCentralBaseFactor :
    letI := A.orderFourActualEllipticBoundaryAction
    Path A.orderFourActualEllipticCentralBase A.orderFourActualEllipticCentralBase := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let x := A.orderFourCayleyPuncturedBasepoint
  let p := A.orderFourFillingRelationCayleyPuncturedLoop
  let y := A.orderFourFillingRelationPrincipalGaugeLoop 0 +
    Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2
  let f := A.orderFourPuncturedProductCentralRealizationMap
  let raw := (p.prod (Path.refl y)).map f.continuous
  have hregular : A.orderFourCollarRegularRepresentativeMap
      A.orderFourActualEllipticBoundaryBase =
        A.orderFourPuncturedProductRegularRealizationMap (x, y) := by
    exact A.orderFourFillingRelationRegularLoop.source.symm |>.trans
      ((A.orderFourRegularLoop_eq_puncturedProductRealization 0).symm.trans
        (congrArg A.orderFourPuncturedProductRegularRealizationMap
          (Prod.ext A.orderFourFillingRelationCayleyPuncturedLoop.source
            A.orderFourPrincipalGaugeWithOffsetPath.source)))
  have hbase : A.orderFourActualEllipticCentralBase = f (x, y) := by
    exact A.orderFourCollarRegularRepresentative_base_projects.symm.trans
      (congrArg A.centralQuotientProjection hregular)
  exact raw.cast hbase hbase

/-- The central fibre-then-base loop is literally the concatenation of its two factors. -/
public theorem orderFourCentralFiberThenBaseLoop_eq_factors :
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourCentralFiberThenBaseLoop =
      A.orderFourCentralFiberFactor.trans A.orderFourCentralBaseFactor := by
  let _ := A.orderFourActualEllipticBoundaryAction
  unfold orderFourCentralFiberThenBaseLoop orderFourRegularFiberThenBaseLoop
    orderFourCentralFiberFactor orderFourCentralBaseFactor
  simp only [Path.map_trans, Path.cast_trans]
  rfl

/-- The same Cayley base factor with the fixed torus coordinate contracted to zero. -/
public noncomputable def orderFourCentralZeroFibreBasePath :
    letI := A.orderFourActualEllipticBoundaryAction
    Path
      (A.orderFourPuncturedProductCentralRealizationMap
        (A.orderFourCayleyPuncturedBasepoint, 0))
      (A.orderFourPuncturedProductCentralRealizationMap
        (A.orderFourCayleyPuncturedBasepoint, 0)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact (A.orderFourFillingRelationCayleyPuncturedLoop.prod (Path.refl 0)).map
    A.orderFourPuncturedProductCentralRealizationMap.continuous

/-- Contract the fixed torus coordinate of the base factor through an explicit vector-cover
representative. -/
public def orderFourCentralBaseFactor_zeroFibreHomotopy :
    letI := A.orderFourActualEllipticBoundaryAction
    ContinuousMap.Homotopy A.orderFourCentralBaseFactor.toContinuousMap
      A.orderFourCentralZeroFibreBasePath.toContinuousMap := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let p := (parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo).1
  let v : ComplexTwoSpace :=
    A.orderFourFillingRelationPrincipalGaugeCoverLift 0 +
      A.orderFourActualEllipticBoundaryBase.2.2
  let f := A.orderFourPuncturedProductCentralRealizationMap
  exact
    { toFun := fun st ↦ f
        (A.orderFourFillingRelationCayleyPuncturedLoop st.2,
          (Quotient.mk _
            (((1 - (st.1 : ℝ) : ℝ) : ℂ) • v) : AdditiveTorus p))
      continuous_toFun := f.continuous.comp <| by
        apply Continuous.prodMk
        · exact A.orderFourFillingRelationCayleyPuncturedLoop.continuous.comp continuous_snd
        · exact (continuous_quot_mk.comp (by fun_prop))
      map_zero_left := by
        intro t
        change f
            (A.orderFourFillingRelationCayleyPuncturedLoop t,
              (Quotient.mk _ (((1 - (0 : ℝ) : ℝ) : ℂ) • v) : AdditiveTorus p)) =
          A.orderFourCentralBaseFactor t
        have hscalar : ((1 - (0 : ℝ) : ℝ) : ℂ) = 1 := by norm_num
        rw [hscalar, one_smul]
        rfl
      map_one_left := by
        intro t
        change f
            (A.orderFourFillingRelationCayleyPuncturedLoop t,
              (Quotient.mk _ (((1 - (1 : ℝ) : ℝ) : ℂ) • v) : AdditiveTorus p)) =
          A.orderFourCentralZeroFibreBasePath t
        have hscalar : ((1 - (1 : ℝ) : ℝ) : ℂ) = 0 := by norm_num
        rw [hscalar, zero_smul]
        rw [additiveTorus_mk_zero]
        rfl }

/-- The base-factor contraction has the same moving-basepoint trace at both loop endpoints. -/
public theorem orderFourCentralBaseFactor_zeroFibreHomotopy_trace :
    letI := A.orderFourActualEllipticBoundaryAction
    let H := A.orderFourCentralBaseFactor_zeroFibreHomotopy
    (H.evalAt 0).cast A.orderFourCentralBaseFactor.source.symm
        A.orderFourCentralZeroFibreBasePath.source.symm =
      (H.evalAt 1).cast A.orderFourCentralBaseFactor.target.symm
        A.orderFourCentralZeroFibreBasePath.target.symm := by
  let _ := A.orderFourActualEllipticBoundaryAction
  apply Path.ext
  funext t
  change A.orderFourPuncturedProductCentralRealizationMap
      (A.orderFourFillingRelationCayleyPuncturedLoop 0, _) =
    A.orderFourPuncturedProductCentralRealizationMap
      (A.orderFourFillingRelationCayleyPuncturedLoop 1, _)
  rw [A.orderFourFillingRelationCayleyPuncturedLoop.source,
    A.orderFourFillingRelationCayleyPuncturedLoop.target]

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
