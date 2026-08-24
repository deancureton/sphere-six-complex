module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
public import SphereSixComplex.Geometry.EllipticFixedPointCriterion
public import SphereSixComplex.Periods.EstablishedFuchsianTorsorDescent
public import SphereSixComplex.Periods.FuchsianCuspNormalization

/-!
# Analytic data selected for the paper construction

This module selects the modular parameter, its descended period functions, the normalized cusp
coordinate, and the standard infinite `A₂` toric model as one dependent package.  Keeping these
choices together ensures that every later filling and collar is built from the same period family.
-/

namespace SphereSixComplex.Geometry

open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.GlobalTorusFamily

noncomputable section

/-- The coherent analytic choices used by all four pieces of the completed family. -/
public structure PaperAnalyticData where
  modular : EstablishedFuchsianModularParameter
  localPeriods : FuchsianPeriodLocalData modular
  cuspCoordinate : CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate modular localPeriods
  toricModel : StandardInfiniteA2ToricModel.Model

/-- The established modular, descent, cusp-normalization, and toric inputs supply one coherent
analytic package. -/
public theorem exists_paperAnalyticData : Nonempty PaperAnalyticData := by
  obtain ⟨E⟩ := exists_establishedFuchsianModularParameter
  obtain ⟨D⟩ := exists_fuchsianPeriodLocalData E
  obtain ⟨N⟩ := FuchsianCuspNormalization.exists_normalizedFuchsianCuspCoordinate E D
  obtain ⟨M⟩ := StandardInfiniteA2ToricModel.Established.model
  exact ⟨⟨E, D, N, M⟩⟩

/-- A fixed coherent choice of the analytic data. -/
@[expose] public noncomputable def paperAnalyticData : PaperAnalyticData :=
  Classical.choice exists_paperAnalyticData

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The actual nondegenerate period family used by the construction. -/
public abbrev periods :
    PeriodFunctions A.modular.modularParameter.toTriangleUniformization :=
  assembledFuchsianPeriodFunctions A.modular A.localPeriods

/-- The actual punctured global torus family to which the three fillings are attached. -/
public abbrev CentralFamily := PuncturedGlobalFamily A.periods

/-- The actual period torus over the order-three fixed point. -/
public abbrev orderThreeTorus :=
  AdditiveTorus
    (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zOne).1

/-- The actual period torus over the order-four fixed point. -/
public abbrev orderFourTorus :=
  AdditiveTorus
    (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1

/-- The paper's free affine order-three action on the disc times its actual fixed fibre. -/
public noncomputable abbrev orderThreeActionData :
    EllipticActionData 3 ComplexUnitDisc A.orderThreeTorus :=
  EllipticFixedPointCriterion.orderThreeActionData A.periods

/-- The paper's free affine order-four action on the disc times its actual fixed fibre. -/
public noncomputable abbrev orderFourActionData :
    EllipticActionData 4 ComplexUnitDisc A.orderFourTorus :=
  EllipticFixedPointCriterion.orderFourActionData A.periods

/-- The completed order-three local filling before it is attached to the global family. -/
public abbrev OrderThreeFilling :=
  letI := A.orderThreeActionData.diagonalAction
  OrbitQuotient (M := ComplexUnitDisc × A.orderThreeTorus) (G := FiniteCyclic 3)

/-- The completed order-four local filling before it is attached to the global family. -/
public abbrev OrderFourFilling :=
  letI := A.orderFourActionData.diagonalAction
  OrbitQuotient (M := ComplexUnitDisc × A.orderFourTorus) (G := FiniteCyclic 4)

/-- The selected order-three filling action is free. -/
public theorem orderThreeAction_free :
    letI := A.orderThreeActionData.diagonalAction
    IsCancelSMul (FiniteCyclic 3) (ComplexUnitDisc × A.orderThreeTorus) :=
  EllipticFixedPointCriterion.orderThreeAction_free A.periods

/-- The selected order-four filling action is free. -/
public theorem orderFourAction_free :
    letI := A.orderFourActionData.diagonalAction
    IsCancelSMul (FiniteCyclic 4) (ComplexUnitDisc × A.orderFourTorus) :=
  EllipticFixedPointCriterion.orderFourAction_free A.periods

end PaperAnalyticData

end


end SphereSixComplex.Geometry
