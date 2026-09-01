module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourBaseFreeHomotopyProof
public import SphereSixComplex.Topology.PaperActualEllipticCentralCoverProductLiftComparison
public import SphereSixComplex.Topology.PaperGeometricCentralPeripheral

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The fixed order-four fibre coordinate of the complete filling loop before removing the
constant collar offset. -/
public noncomputable def orderFourPrincipalGaugeWithOffsetMap :
    letI := A.orderFourActualEllipticBoundaryAction
    C(unitInterval,
      AdditiveTorus
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact
    { toFun := fun t ↦ A.orderFourFillingRelationPrincipalGaugeLoop t +
        Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2
      continuous_toFun := by fun_prop }

/-- Straight contraction of the fixed collar offset in the universal vector cover of the
order-four torus fibre. -/
public def orderFourPrincipalGaugeOffsetHomotopy :
    letI := A.orderFourActualEllipticBoundaryAction
    ContinuousMap.Homotopy A.orderFourPrincipalGaugeWithOffsetMap
      A.orderFourFillingRelationPrincipalGaugeLoop.toContinuousMap := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let p := (parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo).1
  let v := A.orderFourActualEllipticBoundaryBase.2.2
  exact
    { toFun := fun st ↦ A.orderFourFillingRelationPrincipalGaugeLoop st.2 +
        (Quotient.mk _
          (((1 - (st.1 : ℝ) : ℝ) : ℂ) • v) : AdditiveTorus p)
      continuous_toFun := by
        exact (A.orderFourFillingRelationPrincipalGaugeLoop.continuous.comp
          continuous_snd).add
            ((continuous_quot_mk : Continuous (torusProjection p)).comp (by fun_prop))
      map_zero_left := by
        intro t
        change A.orderFourFillingRelationPrincipalGaugeLoop t +
            Quotient.mk _ (((1 - (0 : ℝ) : ℝ) : ℂ) • v) =
          A.orderFourFillingRelationPrincipalGaugeLoop t + Quotient.mk _ v
        simp
      map_one_left := by
        intro t
        change A.orderFourFillingRelationPrincipalGaugeLoop t +
            Quotient.mk _ (((1 - (1 : ℝ) : ℝ) : ℂ) • v) =
          A.orderFourFillingRelationPrincipalGaugeLoop t
        rw [show (((1 - (1 : ℝ) : ℝ) : ℂ) • v) = 0 by simp]
        rw [additiveTorus_mk_zero p, add_zero] }

/-- The base coordinate paired with the exact fixed-fibre coordinate from the local-product
formula. -/
public noncomputable def orderFourBaseGaugeProductMap :
    letI := A.orderFourActualEllipticBoundaryAction
    C(unitInterval,
      TwicePuncturedComplex ×
        AdditiveTorus
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact A.orderFourFillingRelationBaseCoordinateMap.prodMk
    A.orderFourPrincipalGaugeWithOffsetMap

/-- Removing the fixed fibre offset and applying the quartic base homotopy gives the complete
coordinate pair: the positive one-meridian quadruple together with the principal gauge loop. -/
public theorem orderFourBaseGaugeProduct_quadrupleGaugeHomotopy :
    letI := A.orderFourActualEllipticBoundaryAction
    Nonempty (ContinuousMap.Homotopy
      A.orderFourBaseGaugeProductMap
      (twicePuncturedCounterclockwiseOneQuadruple.toContinuousMap.prodMk
        A.orderFourFillingRelationPrincipalGaugeLoop.toContinuousMap)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rcases A.orderFourActualCayleyBaseCoordinate_quadrupleHomotopy with ⟨Hbase⟩
  let Hbase' := Hbase.cast
    A.orderFourFillingRelationBaseCoordinateMap_eq_cayley.symm rfl
  let Hoffset := A.orderFourPrincipalGaugeOffsetHomotopy
  let H₀ : ContinuousMap.Homotopy
      A.orderFourBaseGaugeProductMap
      (A.orderFourFillingRelationBaseCoordinateMap.prodMk
        A.orderFourFillingRelationPrincipalGaugeLoop.toContinuousMap) :=
    { toFun := fun st ↦
        (A.orderFourFillingRelationBaseCoordinateMap st.2, Hoffset st)
      continuous_toFun :=
        (A.orderFourFillingRelationBaseCoordinateMap.continuous.comp continuous_snd).prodMk
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
      (A.orderFourFillingRelationBaseCoordinateMap.prodMk
        A.orderFourFillingRelationPrincipalGaugeLoop.toContinuousMap)
      (twicePuncturedCounterclockwiseOneQuadruple.toContinuousMap.prodMk
        A.orderFourFillingRelationPrincipalGaugeLoop.toContinuousMap) :=
    { toFun := fun st ↦
        (Hbase' st, A.orderFourFillingRelationPrincipalGaugeLoop st.2)
      continuous_toFun := Hbase'.continuous.prodMk
        (A.orderFourFillingRelationPrincipalGaugeLoop.continuous.comp continuous_snd)
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

/-- The zero-section lift of the actual order-four base-coordinate loop. -/
public noncomputable def orderFourZeroSectionBaseMap :
    C(unitInterval, A.CentralFamily) :=
  A.markedBaseToCentralZeroSection.comp A.orderFourFillingRelationBaseCoordinateMap

/-- The zero-section lift of the standard positive four-turn one meridian. -/
public noncomputable def orderFourZeroSectionQuadruplePath :
    Path (A.centralZeroSection A.markedPuncturedBasepoint)
      (A.centralZeroSection A.markedPuncturedBasepoint) :=
  twicePuncturedCounterclockwiseOneQuadruple.map
    A.markedBaseToCentralZeroSection.continuous

/-- The quartic base homotopy lifts literally through the global zero section. -/
public theorem orderFourZeroSectionBase_quadrupleHomotopy :
    Nonempty (ContinuousMap.Homotopy A.orderFourZeroSectionBaseMap
      A.orderFourZeroSectionQuadruplePath.toContinuousMap) := by
  rcases A.orderFourActualCayleyBaseCoordinate_quadrupleHomotopy with ⟨H⟩
  let H' := H.cast A.orderFourFillingRelationBaseCoordinateMap_eq_cayley.symm rfl
  exact ⟨{
    toFun := fun st ↦ A.markedBaseToCentralZeroSection (H' st)
    continuous_toFun := A.markedBaseToCentralZeroSection.continuous.comp H'.continuous
    map_zero_left := by
      intro t
      exact congrArg A.markedBaseToCentralZeroSection (H'.map_zero_left t)
    map_one_left := by
      intro t
      exact congrArg A.markedBaseToCentralZeroSection (H'.map_one_left t) }⟩

/-- The lifted positive four-turn circle is the fourth power of the inverse marked central
one-meridian. -/
public theorem orderFourZeroSectionQuadruplePath_class :
    Path.Homotopic.Quotient.mk A.orderFourZeroSectionQuadruplePath =
      A.markedOneCentralMeridianClass⁻¹ ^ 4 := by
  have h := congrArg
    (FundamentalGroup.map A.markedBaseToCentralZeroSection
      twicePuncturedComplexBasepoint)
    twicePuncturedCounterclockwiseOneQuadruple_class
  rw [map_pow, map_inv, A.markedBaseToCentralZeroSection_map_one] at h
  change (Path.Homotopic.Quotient.mk
      twicePuncturedCounterclockwiseOneQuadruple).map
        A.markedBaseToCentralZeroSection = _ at h
  rw [← Path.Homotopic.Quotient.mk_map] at h
  exact h

/-- Rebase the lifted four-turn zero-section circle at the selected actual cusp point. -/
public noncomputable def orderFourActualCuspZeroSectionQuadruplePath :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  A.actualCuspMarkedCentralWhisker.symm.trans
    (A.orderFourZeroSectionQuadruplePath.trans A.actualCuspMarkedCentralWhisker)

/-- At the actual cusp basepoint, the zero-section part is the fourth power of the geometric
second central meridian. -/
public theorem orderFourActualCuspZeroSectionQuadruplePath_class :
    Path.Homotopic.Quotient.mk A.orderFourActualCuspZeroSectionQuadruplePath =
      A.geometricCentralRhoTwo ^ 4 := by
  have h := congrArg A.markedCentralToActualCuspEquiv
    A.orderFourZeroSectionQuadruplePath_class
  rw [map_pow] at h
  exact h

/-- The straight vector-cover segment with the same period endpoint as the order-four
principal gauge. -/
public noncomputable def orderFourPrincipalGaugeStraightLiftPath :
    letI := A.orderFourActualEllipticBoundaryAction
    Path (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)
      (A.orderFourFillingRelationPrincipalGaugeDeck •
        A.orderFourFillingRelationPrincipalGaugeCoverLift 0) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact Path.segment _ _

/-- The fixed-fibre loop obtained by projecting the straight negative-epsilon-prime period
segment. -/
public noncomputable def orderFourPrincipalGaugeStraightLoop :
    letI := A.orderFourActualEllipticBoundaryAction
    Path
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1
        (A.orderFourFillingRelationPrincipalGaugeCoverLift 0))
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1
        (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : ProperlyDiscontinuousSMul
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1)
      ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul
      (FullRank.ofSetupInequalities _
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).2)
  let hp : IsQuotientCoveringMap
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1)
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  exact projectedQuotientDeckPath hp
    (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)
    A.orderFourFillingRelationPrincipalGaugeDeck
    A.orderFourPrincipalGaugeStraightLiftPath

/-- The analytic principal gauge and the literal straight negative-epsilon-prime period loop
have the same fixed-torus path class. -/
public theorem orderFourFillingRelationPrincipalGaugeLoop_class_eq_straight :
    letI := A.orderFourActualEllipticBoundaryAction
    pathLoopClass A.orderFourFillingRelationPrincipalGaugeLoop =
      pathLoopClass A.orderFourPrincipalGaugeStraightLoop := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : ProperlyDiscontinuousSMul
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1)
      ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul
      (FullRank.ofSetupInequalities _
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).2)
  let hp : IsQuotientCoveringMap
      (torusProjection
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1)
      (PeriodGroup
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1) :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let e : (torusProjection
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1) ⁻¹'
        {torusProjection
          (parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo).1
          (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)} :=
    ⟨A.orderFourFillingRelationPrincipalGaugeCoverLift 0, rfl⟩
  apply (hp.fundamentalGroupEquiv e).injective
  change hp.fundamentalGroupToMulOpposite e
      (pathLoopClass A.orderFourFillingRelationPrincipalGaugeLoop) =
    hp.fundamentalGroupToMulOpposite e
      (pathLoopClass A.orderFourPrincipalGaugeStraightLoop)
  rw [A.orderFourFillingRelationPrincipalGaugeLoop_classification]
  exact (fundamentalGroupToMulOpposite_projectedQuotientDeckPath hp
    (A.orderFourFillingRelationPrincipalGaugeCoverLift 0)
    A.orderFourFillingRelationPrincipalGaugeDeck
    A.orderFourPrincipalGaugeStraightLiftPath).symm

/-- The literal negative-epsilon-prime period loop over the chosen marked regular-base lift,
projected to the central family and based at the marked zero-section point. -/
public noncomputable def orderFourMarkedCentralNegEpsilonPrimePeriodPath :
    Path (A.centralZeroSection A.markedPuncturedBasepoint)
      (A.centralZeroSection A.markedPuncturedBasepoint) :=
  ((regularFamilyPeriodLoop A.periods
      (A.markedRegularBaseLift, (0 : ComplexTwoSpace)) (-epsilon')).map
        (regularFamilyQuotientMap A.periods).continuous).cast
    A.markedCentralBase_eq_lift A.markedCentralBase_eq_lift

/-- The literal marked period path represents the marked translation with label
negative epsilon prime. -/
public theorem orderFourMarkedCentralNegEpsilonPrimePeriodPath_class :
    Path.Homotopic.Quotient.mk A.orderFourMarkedCentralNegEpsilonPrimePeriodPath =
      Additive.toMul (A.markedCentralTranslation (-epsilon')) := by
  unfold markedCentralTranslation markedCentralBaseEquiv centralTranslationAtZero
  simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
    Function.comp_apply, toMul_ofMul]
  rw [regularFamilyTranslationAtZero_apply_eq_periodLoop]
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  change Path.Homotopic.Quotient.mk A.orderFourMarkedCentralNegEpsilonPrimePeriodPath =
    SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq
      A.markedCentralBase_eq_lift.symm
      (Path.Homotopic.Quotient.mk
        ((regularFamilyPeriodLoop A.periods
          (A.markedRegularBaseLift, (0 : ComplexTwoSpace)) (-epsilon')).map
            (regularFamilyQuotientMap A.periods).continuous))
  rw [SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq_apply]
  unfold orderFourMarkedCentralNegEpsilonPrimePeriodPath
  exact Path.Homotopic.Quotient.mk_cast _ _ _

/-- Rebase the marked literal negative-epsilon-prime period path at the selected actual cusp
point. -/
public noncomputable def orderFourActualCuspMarkedNegEpsilonPrimePeriodPath :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  A.actualCuspMarkedCentralWhisker.symm.trans
    (A.orderFourMarkedCentralNegEpsilonPrimePeriodPath.trans
      A.actualCuspMarkedCentralWhisker)

/-- The rebased literal period path represents the transported geometric translation. -/
public theorem orderFourActualCuspMarkedNegEpsilonPrimePeriodPath_class :
    Path.Homotopic.Quotient.mk A.orderFourActualCuspMarkedNegEpsilonPrimePeriodPath =
      Additive.toMul (A.geometricCentralTranslation (-epsilon')) := by
  have h := congrArg A.markedCentralToActualCuspEquiv
    A.orderFourMarkedCentralNegEpsilonPrimePeriodPath_class
  exact h

/-- A literal global loop representing the geometric order-four meridian relator with its
negative-epsilon-prime period contribution. -/
public noncomputable def orderFourActualCuspGeometricRelatorPath :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  A.orderFourActualCuspMarkedNegEpsilonPrimePeriodPath.trans
    A.orderFourActualCuspZeroSectionQuadruplePath

/-- The explicit global representative has the expected order-four geometric product class. -/
public theorem orderFourActualCuspGeometricRelatorPath_class :
    Path.Homotopic.Quotient.mk A.orderFourActualCuspGeometricRelatorPath =
      A.geometricCentralRhoTwo ^ 4 *
        (Additive.toMul (A.geometricCentralTranslation epsilon'))⁻¹ := by
  rw [orderFourActualCuspGeometricRelatorPath,
    Path.Homotopic.Quotient.mk_trans,
    A.orderFourActualCuspZeroSectionQuadruplePath_class,
    A.orderFourActualCuspMarkedNegEpsilonPrimePeriodPath_class]
  rw [map_neg, toMul_neg]
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
