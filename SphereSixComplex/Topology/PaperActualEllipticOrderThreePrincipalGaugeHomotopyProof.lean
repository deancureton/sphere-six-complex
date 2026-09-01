module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeBaseFreeHomotopyProof
public import SphereSixComplex.Topology.PaperActualEllipticCentralCoverProductLiftComparison

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization

variable (A : PaperAnalyticData)

/-- The fixed order-three fibre coordinate of the complete filling loop before removing the
constant collar offset. -/
public noncomputable def orderThreePrincipalGaugeWithOffsetMap :
    letI := A.orderThreeActualEllipticBoundaryAction
    C(unitInterval,
      AdditiveTorus
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact
    { toFun := fun t ↦ A.orderThreeFillingRelationPrincipalGaugeLoop t +
        Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2
      continuous_toFun := by fun_prop }

/-- Straight contraction of the fixed collar offset in the universal vector cover of the
order-three torus fibre. -/
public def orderThreePrincipalGaugeOffsetHomotopy :
    letI := A.orderThreeActualEllipticBoundaryAction
    ContinuousMap.Homotopy A.orderThreePrincipalGaugeWithOffsetMap
      A.orderThreeFillingRelationPrincipalGaugeLoop.toContinuousMap := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let p := (parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne).1
  let v := A.orderThreeActualEllipticBoundaryBase.2.2
  exact
    { toFun := fun st ↦ A.orderThreeFillingRelationPrincipalGaugeLoop st.2 +
        (Quotient.mk _
          (((1 - (st.1 : ℝ) : ℝ) : ℂ) • v) : AdditiveTorus p)
      continuous_toFun := by
        exact (A.orderThreeFillingRelationPrincipalGaugeLoop.continuous.comp
          continuous_snd).add
            ((continuous_quot_mk : Continuous (torusProjection p)).comp (by fun_prop))
      map_zero_left := by
        intro t
        change A.orderThreeFillingRelationPrincipalGaugeLoop t +
            Quotient.mk _ (((1 - (0 : ℝ) : ℝ) : ℂ) • v) =
          A.orderThreeFillingRelationPrincipalGaugeLoop t + Quotient.mk _ v
        simp
      map_one_left := by
        intro t
        change A.orderThreeFillingRelationPrincipalGaugeLoop t +
            Quotient.mk _ (((1 - (1 : ℝ) : ℝ) : ℂ) • v) =
          A.orderThreeFillingRelationPrincipalGaugeLoop t
        rw [show (((1 - (1 : ℝ) : ℝ) : ℂ) • v) = 0 by simp]
        rw [additiveTorus_mk_zero p, add_zero] }

/-- The base coordinate paired with the exact fixed-fibre coordinate from the local-product
formula. -/
public noncomputable def orderThreeBaseGaugeProductMap :
    letI := A.orderThreeActualEllipticBoundaryAction
    C(unitInterval,
      TwicePuncturedComplex ×
        AdditiveTorus
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne).1) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact A.orderThreeFillingRelationBaseCoordinateMap.prodMk
    A.orderThreePrincipalGaugeWithOffsetMap

/-- Removing the fixed fibre offset and applying the cubic base homotopy gives the complete
coordinate pair: the positive zero-meridian cube together with the principal gauge loop. -/
public theorem orderThreeBaseGaugeProduct_tripleGaugeHomotopy :
    letI := A.orderThreeActualEllipticBoundaryAction
    Nonempty (ContinuousMap.Homotopy
      A.orderThreeBaseGaugeProductMap
      (twicePuncturedCounterclockwiseZeroTriple.toContinuousMap.prodMk
        A.orderThreeFillingRelationPrincipalGaugeLoop.toContinuousMap)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rcases A.orderThreeActualCayleyBaseCoordinate_tripleHomotopy with ⟨Hbase⟩
  let Hbase' := Hbase.cast
    A.orderThreeFillingRelationBaseCoordinateMap_eq_cayley.symm rfl
  let Hoffset := A.orderThreePrincipalGaugeOffsetHomotopy
  let H₀ : ContinuousMap.Homotopy
      A.orderThreeBaseGaugeProductMap
      (A.orderThreeFillingRelationBaseCoordinateMap.prodMk
        A.orderThreeFillingRelationPrincipalGaugeLoop.toContinuousMap) :=
    { toFun := fun st ↦
        (A.orderThreeFillingRelationBaseCoordinateMap st.2, Hoffset st)
      continuous_toFun :=
        (A.orderThreeFillingRelationBaseCoordinateMap.continuous.comp continuous_snd).prodMk
          Hoffset.continuous
      map_zero_left := by
        intro t
        apply Prod.ext
        · rfl
        · exact Hoffset.map_zero_left t
      map_one_left := by
        intro t
        apply Prod.ext
        · rfl
        · exact Hoffset.map_one_left t }
  let H₁ : ContinuousMap.Homotopy
      (A.orderThreeFillingRelationBaseCoordinateMap.prodMk
        A.orderThreeFillingRelationPrincipalGaugeLoop.toContinuousMap)
      (twicePuncturedCounterclockwiseZeroTriple.toContinuousMap.prodMk
        A.orderThreeFillingRelationPrincipalGaugeLoop.toContinuousMap) :=
    { toFun := fun st ↦
        (Hbase' st, A.orderThreeFillingRelationPrincipalGaugeLoop st.2)
      continuous_toFun := Hbase'.continuous.prodMk
        (A.orderThreeFillingRelationPrincipalGaugeLoop.continuous.comp continuous_snd)
      map_zero_left := by
        intro t
        apply Prod.ext
        · exact Hbase'.map_zero_left t
        · rfl
      map_one_left := by
        intro t
        apply Prod.ext
        · exact Hbase'.map_one_left t
        · rfl }
  exact ⟨H₀.trans H₁⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
