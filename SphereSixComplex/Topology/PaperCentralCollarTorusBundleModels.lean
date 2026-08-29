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

/-- A finite-CW four-torus-bundle homotopy model for the regular global quotient. -/
public axiom centralFamilyBundleRealization
    (A : SphereSixComplex.Geometry.PaperAnalyticData) :
    AdditiveFourTorusBundleRealization A.openEmbeddingStarData.central

/-- A finite-CW four-torus-bundle homotopy model for each common collar quotient. -/
public axiom collarBundleRealization
    (A : SphereSixComplex.Geometry.PaperAnalyticData) (i : Fin 3) :
    AdditiveFourTorusBundleRealization (A.openEmbeddingStarData.collarSource i)

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
