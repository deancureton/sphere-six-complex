module

public import SphereSixComplex.Geometry.EllipticFamilySpecialization
public import SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels
public import SphereSixComplex.Topology.SectionSevenLocalEulerModels

/-!
# Four-torus bundle models for the central family and collars

The analytic files construct the relevant quotient spaces and local diffeomorphisms, but Mathlib
has no theorem turning these equivariant varying-lattice quotients into finite-CW fibre bundles.
This file isolates that exact geometric realization boundary.  It contains no homology or Euler
assertion.  Given the independent standard CW model of a full-rank additive complex torus, it
constructs the `FourTorusBundleModel` witnesses required by the Section 7 local calculation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContinuousMap

namespace SphereSixComplex

namespace FourTorusCellModel

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Transport a four-torus cell model from a homeomorphic model space. -/
public noncomputable def pullbackHomeomorph
    (M : FourTorusCellModel X) (e : Y ≃ₜ X) : FourTorusCellModel Y where
  toFiniteCWModelSix := by
    let _ := M.toFiniteCWModelSix.topology
    exact
      { Carrier := M.toFiniteCWModelSix.Carrier
        topology := inferInstance
        t2 := M.toFiniteCWModelSix.t2
        homotopyEquiv := e.toHomotopyEquiv.trans M.toFiniteCWModelSix.homotopyEquiv
        cwComplex := M.toFiniteCWModelSix.cwComplex
        finite := M.toFiniteCWModelSix.finite
        cellsAboveSix := M.toFiniteCWModelSix.cellsAboveSix }
  cellsZero := M.cellsZero
  cellsOne := M.cellsOne
  cellsTwo := M.cellsTwo
  cellsThree := M.cellsThree
  cellsFour := M.cellsFour
  cellsFive := M.cellsFive
  cellsSix := M.cellsSix

end FourTorusCellModel

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

/-- Insert the independent standard four-torus CW model for the identified additive fibre. -/
public noncomputable def toFourTorusBundleModel
    (R : AdditiveFourTorusBundleRealization X)
    (fiberCells : FourTorusCellModel
      (SphereSixComplex.Geometry.EllipticFamilySpecialization.AdditiveTorus
        R.fiberParameter)) :
    FourTorusBundleModel X where
  toFiniteCWBundleModelSix := R.toFiniteCWBundleModelSix
  fiberCells := by
    let _ := R.toFiniteCWBundleModelSix.fiberTopology
    exact fiberCells.pullbackHomeomorph R.fiberHomeomorph

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
    (EstablishedFiniteCWTopology.additiveTorusFourTorusCellModel
      R.fiberParameter R.fiberFullRank)

/-- Every actual cusp or elliptic collar source has the required four-torus bundle model. -/
public noncomputable def collarFourTorusBundleModel
    (i : Fin 3) : FourTorusBundleModel (A.openEmbeddingStarData.collarSource i) :=
  let R := EstablishedTorusBundleTopology.collarBundleRealization A i
  R.toFourTorusBundleModel
    (EstablishedFiniteCWTopology.additiveTorusFourTorusCellModel
      R.fiberParameter R.fiberFullRank)

end Geometry.PaperAnalyticData

end SphereSixComplex
