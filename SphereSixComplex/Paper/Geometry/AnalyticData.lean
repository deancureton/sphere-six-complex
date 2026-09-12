module

public import SphereSixComplex.Paper.Geometry.StandardInfiniteA2ToricCarrierGeometryAssembly
public import SphereSixComplex.Paper.Geometry.EllipticFixedPointCriterion
public import SphereSixComplex.Paper.Periods.EstablishedFuchsianTorsorDescent
public import SphereSixComplex.Paper.Periods.FuchsianCuspNormalization

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
public structure AnalyticData where
  modular : FuchsianModularLift
  periodData : FuchsianPeriodData modular
  cuspCoordinate : CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate modular periodData

/-- Global affine torsor sections and the Schur shift determine one coherent period family. -/
@[expose] public noncomputable def AnalyticData.ofFrame
    (E : FuchsianModularLift) (F : ModularNegOneFrame E) : AnalyticData := by
  let D := Classical.choice (FuchsianAffineDescent.nonempty_fuchsianPeriodData E F)
  let N := Classical.choice
    (FuchsianCuspNormalization.exists_normalizedFuchsianCuspCoordinate E D)
  exact ⟨E, D, N⟩

/-- A coherent production choice of all analytic inputs. -/
@[expose] public noncomputable def analyticData : AnalyticData :=
  let E := Classical.choice nonempty_fuchsianModularLift
  let F := Classical.choice (nonempty_modularNegOneFrame E)
  AnalyticData.ofFrame E F


namespace AnalyticData

variable (A : AnalyticData)

/-- The actual nondegenerate period family used by the construction. -/
public abbrev periods :
    PeriodFunctions A.modular.modularParameter.toTriangleUniformization :=
  assembledFuchsianPeriodFunctions A.modular A.periodData

/-- The actual punctured global torus family to which the three fillings are attached. -/
public abbrev CentralFamily := PuncturedGlobalFamily A.periods

/-- The actual period torus over the order-three fixed point. -/
public abbrev OrderThreeTorus :=
  AdditiveTorus
    (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zOne).1

/-- The actual period torus over the order-four fixed point. -/
public abbrev OrderFourTorus :=
  AdditiveTorus
    (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1







end AnalyticData

end


end SphereSixComplex.Geometry
