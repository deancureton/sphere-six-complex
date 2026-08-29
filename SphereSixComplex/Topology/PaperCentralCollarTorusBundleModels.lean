module

public import SphereSixComplex.Geometry.EllipticFamilySpecialization
public import SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels
public import SphereSixComplex.Topology.SectionSevenLocalEulerModels

/-!
# Four-torus bundle models for the central family and collars

The analytic files construct the relevant quotient spaces and local diffeomorphisms, but Mathlib
has no theorem turning these equivariant varying-lattice quotients into finite-CW fibre bundles.
This file isolates that exact geometric realization boundary.  It contains no homology or Euler
assertion.  The fibre's homological model is supplied by its explicit identification with the
standard four-torus.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContinuousMap

namespace SphereSixComplex

/-- A finite-CW bundle realization together with an identification of its model fibre with one
actual full-rank additive complex torus.  This is geometric data only. -/
public structure AdditiveFourTorusBundleRealization
    (X : Type) [TopologicalSpace X] where
  toFiniteCWBundleModelSix : FiniteCWBundleModelSix X
  fiberParameter : SphereSixComplex.Periods.Parameters
  fiberFullRank : SphereSixComplex.Geometry.ComplexTorus.FullRank fiberParameter
  fiberHomeomorph :
    let _ := toFiniteCWBundleModelSix.fiberTopology
    toFiniteCWBundleModelSix.Fiber ≃ₜ
      SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus fiberParameter

namespace AdditiveFourTorusBundleRealization

variable {X : Type} [TopologicalSpace X]

/-- Insert the proved four-torus homological model for the identified additive fibre. -/
public noncomputable def toFourTorusBundleModel
    (R : AdditiveFourTorusBundleRealization X)
    (fiberHomology : FourTorusHomologicalModel
      (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus
        R.fiberParameter)) :
    FourTorusBundleModel X where
  toFiniteCWBundleModelSix := R.toFiniteCWBundleModelSix
  fiberHomology := by
    let _ := R.toFiniteCWBundleModelSix.fiberTopology
    exact fiberHomology.homeomorph R.fiberHomeomorph

end AdditiveFourTorusBundleRealization

namespace EstablishedTorusBundleTopology

/-- The simultaneous finite-CW bundle realization of the central family and its three collars,
with every model fibre identified with the actual order-three period torus of the paper family. -/
public structure CentralCollarBundleGeometricRealization
    (A : SphereSixComplex.Geometry.PaperAnalyticData) where
  centralModel : FiniteCWBundleModelSix A.openEmbeddingStarData.central
  centralFiberHomeomorph :
    let _ := centralModel.fiberTopology
    centralModel.Fiber ≃ₜ A.orderThreeTorus
  collarModel : ∀ i : Fin 3,
    FiniteCWBundleModelSix (A.openEmbeddingStarData.collarSource i)
  collarFiberHomeomorph : ∀ i : Fin 3,
    let _ := (collarModel i).fiberTopology
    (collarModel i).Fiber ≃ₜ A.orderThreeTorus

/-- The exact geometric input that the present Mathlib fibre-bundle API does not construct from
the equivariant varying-lattice quotient.  One simultaneous witness supplies the global family
and all three collars, with a common actual period-torus fibre. -/
public axiom centralCollarBundleGeometricRealization
    (A : SphereSixComplex.Geometry.PaperAnalyticData) :
    Nonempty (CentralCollarBundleGeometricRealization A)

/-- A finite-CW four-torus-bundle homotopy model for the regular global quotient. -/
public noncomputable def centralFamilyBundleRealization
    (A : SphereSixComplex.Geometry.PaperAnalyticData) :
    AdditiveFourTorusBundleRealization A.openEmbeddingStarData.central := by
  let R := Classical.choice (centralCollarBundleGeometricRealization A)
  let p := SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
  exact
    { toFiniteCWBundleModelSix := R.centralModel
      fiberParameter := p.1
      fiberFullRank := SphereSixComplex.Geometry.ComplexTorus.FullRank.ofSetupInequalities p.1 p.2
      fiberHomeomorph := R.centralFiberHomeomorph }

/-- A finite-CW four-torus-bundle homotopy model for each common collar quotient. -/
public noncomputable def collarBundleRealization
    (A : SphereSixComplex.Geometry.PaperAnalyticData) (i : Fin 3) :
    AdditiveFourTorusBundleRealization (A.openEmbeddingStarData.collarSource i) := by
  let R := Classical.choice (centralCollarBundleGeometricRealization A)
  let p := SphereSixComplex.Geometry.AnalyticTorusFamily.parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
  exact
    { toFiniteCWBundleModelSix := R.collarModel i
      fiberParameter := p.1
      fiberFullRank := SphereSixComplex.Geometry.ComplexTorus.FullRank.ofSetupInequalities p.1 p.2
      fiberHomeomorph := R.collarFiberHomeomorph i }

end EstablishedTorusBundleTopology

namespace Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The actual central family has the required four-torus bundle model. -/
public noncomputable def centralFourTorusBundleModel :
    FourTorusBundleModel A.openEmbeddingStarData.central :=
  let R := EstablishedTorusBundleTopology.centralFamilyBundleRealization A
  R.toFourTorusBundleModel
    (EstablishedFiniteCWTopology.additiveTorusFourTorusHomologicalModel
      R.fiberParameter R.fiberFullRank)

/-- Every actual cusp or elliptic collar source has the required four-torus bundle model. -/
public noncomputable def collarFourTorusBundleModel
    (i : Fin 3) : FourTorusBundleModel (A.openEmbeddingStarData.collarSource i) :=
  let R := EstablishedTorusBundleTopology.collarBundleRealization A i
  R.toFourTorusBundleModel
    (EstablishedFiniteCWTopology.additiveTorusFourTorusHomologicalModel
      R.fiberParameter R.fiberFullRank)

end Geometry.PaperAnalyticData

end SphereSixComplex
