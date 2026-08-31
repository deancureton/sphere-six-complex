module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCarrierGeometryAssembly
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

/-- Every analytic package in this development uses the explicitly constructed standard
infinite `A₂` toric model. -/
public abbrev PaperAnalyticData.toricModel (_A : PaperAnalyticData) :
    StandardInfiniteA2ToricModel.Model :=
  StandardInfiniteA2ToricModel.Construction.constructedModel

/-- The established modular, explicit affine-descent, cusp-normalization, and toric inputs supply
one coherent analytic package. -/
public theorem exists_paperAnalyticData
    (E : EstablishedFuchsianModularParameter)
    (F : ExactLiftedModularNegOneFrame E)
    (Amu : (fuchsianMuDescentProblem E F).AnalyticDescentData)
    (Abeta : FuchsianBetaAnalyticDescentData E F Amu) :
    Nonempty PaperAnalyticData := by
  obtain ⟨D⟩ := exists_fuchsianPeriodLocalData E F Amu Abeta
  obtain ⟨N⟩ := FuchsianCuspNormalization.exists_normalizedFuchsianCuspCoordinate E D
  exact ⟨⟨E, D, N⟩⟩

/-- The standard analytic descent theorem supplies the dependent `mu` and `beta` certificates
needed for the coherent paper package. -/
public theorem exists_paperAnalyticData_of_establishedAnalyticDescent
    (E : EstablishedFuchsianModularParameter)
    (F : ExactLiftedModularNegOneFrame E) :
    Nonempty PaperAnalyticData :=
  exists_paperAnalyticData E F
    (establishedFuchsianMuAnalyticDescentData E F)
    (establishedFuchsianBetaAnalyticDescentData E F)

/-- The established modular parameter, modular frame, general analytic descent, cusp
normalization, and toric model produce the coherent analytic package unconditionally. -/
public theorem exists_establishedPaperAnalyticData : Nonempty PaperAnalyticData := by
  obtain ⟨E⟩ := exists_establishedFuchsianModularParameter
  obtain ⟨F⟩ := establishedExactLiftedModularNegOneFrame E
  exact exists_paperAnalyticData_of_establishedAnalyticDescent E F

/-- A coherent choice of the analytic data supplied by concrete affine-descent certificates. -/
@[expose] public noncomputable def paperAnalyticData
    (E : EstablishedFuchsianModularParameter)
    (F : ExactLiftedModularNegOneFrame E)
    (Amu : (fuchsianMuDescentProblem E F).AnalyticDescentData)
    (Abeta : FuchsianBetaAnalyticDescentData E F Amu) :
    PaperAnalyticData := by
  let D := Classical.choice (exists_fuchsianPeriodLocalData E F Amu Abeta)
  let N := Classical.choice
    (FuchsianCuspNormalization.exists_normalizedFuchsianCuspCoordinate E D)
  exact ⟨E, D, N⟩

/-- A coherent production choice requiring only the exact modular parameter and modular frame. -/
@[expose] public noncomputable def paperAnalyticDataOfEstablishedAnalyticDescent
    (E : EstablishedFuchsianModularParameter)
    (F : ExactLiftedModularNegOneFrame E) : PaperAnalyticData :=
  paperAnalyticData E F
    (establishedFuchsianMuAnalyticDescentData E F)
    (establishedFuchsianBetaAnalyticDescentData E F)

/-- A coherent production choice of all analytic inputs. -/
@[expose] public noncomputable def establishedPaperAnalyticData : PaperAnalyticData :=
  let E := Classical.choice exists_establishedFuchsianModularParameter
  let F := Classical.choice (establishedExactLiftedModularNegOneFrame E)
  paperAnalyticDataOfEstablishedAnalyticDescent E F

@[simp]
public theorem PaperAnalyticData.toricModel_eq_constructed (A : PaperAnalyticData) :
    A.toricModel =
      StandardInfiniteA2ToricModel.Construction.constructedModel := by
  rfl

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
