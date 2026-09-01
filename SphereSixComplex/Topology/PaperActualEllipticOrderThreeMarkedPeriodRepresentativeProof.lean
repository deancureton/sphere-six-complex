module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreePrincipalGaugeStraighteningProof

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The literal `epsilon`-period loop over the chosen marked regular-base lift, projected to the
central family and based at the marked zero-section point. -/
public noncomputable def orderThreeMarkedCentralEpsilonPeriodPath :
    Path (A.centralZeroSection A.markedPuncturedBasepoint)
      (A.centralZeroSection A.markedPuncturedBasepoint) :=
  ((regularFamilyPeriodLoop A.periods
      (A.markedRegularBaseLift, (0 : ComplexTwoSpace)) epsilon).map
        (regularFamilyQuotientMap A.periods).continuous).cast
    A.markedCentralBase_eq_lift A.markedCentralBase_eq_lift

/-- The literal marked period path represents the marked translation with label `epsilon`. -/
public theorem orderThreeMarkedCentralEpsilonPeriodPath_class :
    Path.Homotopic.Quotient.mk A.orderThreeMarkedCentralEpsilonPeriodPath =
      Additive.toMul (A.markedCentralTranslation epsilon) := by
  unfold markedCentralTranslation markedCentralBaseEquiv centralTranslationAtZero
  simp only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
    Function.comp_apply, toMul_ofMul]
  rw [regularFamilyTranslationAtZero_apply_eq_periodLoop]
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  change Path.Homotopic.Quotient.mk A.orderThreeMarkedCentralEpsilonPeriodPath =
    SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq
      A.markedCentralBase_eq_lift.symm
      (Path.Homotopic.Quotient.mk
        ((regularFamilyPeriodLoop A.periods
          (A.markedRegularBaseLift, (0 : ComplexTwoSpace)) epsilon).map
            (regularFamilyQuotientMap A.periods).continuous))
  rw [SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq_apply]
  unfold orderThreeMarkedCentralEpsilonPeriodPath
  exact Path.Homotopic.Quotient.mk_cast _ _ _

/-- Rebase the marked literal `epsilon`-period path at the selected actual cusp point. -/
public noncomputable def orderThreeActualCuspMarkedEpsilonPeriodPath :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  A.actualCuspMarkedCentralWhisker.symm.trans
    (A.orderThreeMarkedCentralEpsilonPeriodPath.trans A.actualCuspMarkedCentralWhisker)

/-- The rebased literal period path represents the transported geometric translation. -/
public theorem orderThreeActualCuspMarkedEpsilonPeriodPath_class :
    Path.Homotopic.Quotient.mk A.orderThreeActualCuspMarkedEpsilonPeriodPath =
      Additive.toMul (A.geometricCentralTranslation epsilon) := by
  have h := congrArg A.markedCentralToActualCuspEquiv
    A.orderThreeMarkedCentralEpsilonPeriodPath_class
  exact h

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
