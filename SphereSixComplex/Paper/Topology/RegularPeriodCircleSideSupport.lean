module
public import SphereSixComplex.Paper.Topology.RegularPeriodCircleTransport
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology GlobalTorusFamily TriangleGroup ComplexTorus

public def regularPeriodCircleToInterior (A : PaperAnalyticData) (n : IntegerPeriods) :
    C(UnitAddCircle × RegularBase (U := A.modular.modularParameter.toTriangleUniformization),
      A.SectionSevenEllipticInterior) :=
  ⟨fun p ↦ (A.sectionSevenEllipticCentralImageHomeomorph.symm
    (regularPeriodCircleInGlobal A.periods n p)).1,
    continuous_subtype_val.comp (A.sectionSevenEllipticCentralImageHomeomorph.symm.continuous.comp
      (regularPeriodCircleInGlobal A.periods n).continuous)⟩

public theorem regularPeriodCircleInGlobal_coordinate (A : PaperAnalyticData)
    (n : IntegerPeriods) (t : UnitAddCircle)
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :
    A.centralFamilyCoordinate (regularPeriodCircleInGlobal A.periods n (t, b)) =
      A.puncturedBaseHomeomorphTwicePuncturedComplex (Quotient.mk _ b) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  change A.centralFamilyCoordinate (A.centralQuotientProjection
    (regularPeriodCircle A.periods n ((r : UnitAddCircle), b))) = _
  rw [regularPeriodCircle_real]
  rfl

public theorem regularPeriodCircleToInterior_mem_three {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) (n : IntegerPeriods) (t : UnitAddCircle)
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (hb : (A.puncturedBaseHomeomorphTwicePuncturedComplex (Quotient.mk _ b)).1.re < 2 / 3) :
    A.regularPeriodCircleToInterior n (t, b) ∈ R.twoDiscCover.orderThreeSide := by
  change _ ∈ A.sectionSevenActualAffineSplit.allocation.orderThreeSide
  refine Or.inr ⟨A.sectionSevenEllipticCentralImageHomeomorph.symm
    (regularPeriodCircleInGlobal A.periods n (t, b)), ?_, rfl⟩
  change (A.centralFamilyCoordinate (A.sectionSevenEllipticCentralImageHomeomorph
    (A.sectionSevenEllipticCentralImageHomeomorph.symm _))).1.re < _
  rw [Homeomorph.apply_symm_apply, regularPeriodCircleInGlobal_coordinate]
  exact hb

public theorem regularPeriodCircleToInterior_mem_four {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) (n : IntegerPeriods) (t : UnitAddCircle)
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (hb : 1 / 3 < (A.puncturedBaseHomeomorphTwicePuncturedComplex (Quotient.mk _ b)).1.re) :
    A.regularPeriodCircleToInterior n (t, b) ∈ R.twoDiscCover.orderFourSide := by
  change _ ∈ A.sectionSevenActualAffineSplit.allocation.orderFourSide
  refine Or.inr ⟨A.sectionSevenEllipticCentralImageHomeomorph.symm
    (regularPeriodCircleInGlobal A.periods n (t, b)), ?_, rfl⟩
  change _ < (A.centralFamilyCoordinate (A.sectionSevenEllipticCentralImageHomeomorph
    (A.sectionSevenEllipticCentralImageHomeomorph.symm _))).1.re
  rw [Homeomorph.apply_symm_apply, regularPeriodCircleInGlobal_coordinate]
  exact hb

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
