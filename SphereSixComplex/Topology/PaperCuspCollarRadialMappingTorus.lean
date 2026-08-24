module

public import SphereSixComplex.Topology.CircleMappingTorusHomologyBases
public import SphereSixComplex.Topology.PaperCollarMappingTorusAdapters
public import SphereSixComplex.Topology.PaperEllipticCollarFundamentalDomain
public import Mathlib.Analysis.Convex.Contractible

/-!
# The radial mapping-torus model of the cusp collar

A punctured cusp collar retains an open radial coordinate.  Thus its dimensionally correct model
is an open interval times a four-torus mapping torus.  The interval is contractible, so this model
still supplies the Wang bases required in degrees one and two.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContinuousMap

namespace SphereSixComplex

/-- The open radial interval is contractible when its radius is positive. -/
public noncomputable def openRadialIntervalHomotopyEquivUnit
    {r : ℝ} (hr : 0 < r) : OpenRadialInterval r ≃ₕ Unit := by
  letI : ContractibleSpace (OpenRadialInterval r) :=
    (convex_Ioo (0 : ℝ) r).contractibleSpace (nonempty_Ioo.mpr hr)
  exact Classical.choice (ContractibleSpace.hequiv_unit (OpenRadialInterval r))

/-- A contractible radial factor can be removed up to homotopy equivalence. -/
public noncomputable def openRadialIntervalProdHomotopyEquiv
    {X : Type} [TopologicalSpace X] {r : ℝ} (hr : 0 < r) :
    OpenRadialInterval r × X ≃ₕ X :=
  ((openRadialIntervalHomotopyEquivUnit hr).prodCongr
      (ContinuousMap.HomotopyEquiv.refl X)).trans
    (Homeomorph.uniqueProd Unit X).toHomotopyEquiv

namespace Geometry.PaperAnalyticData

open SphereSixComplex.CircleMappingTorusHomologyBases

variable (A : PaperAnalyticData)

/-- The dimensionally correct clutching realization of the actual punctured cusp collar. -/
public structure CuspCollarRadialMappingTorusRealization where
  radius : ℝ
  radius_pos : 0 < radius
  Fiber : Type
  fiberTopology : TopologicalSpace Fiber
  clutching : let _ := fiberTopology; Fiber ≃ₜ Fiber
  totalHomeomorph : let _ := fiberTopology
    A.openEmbeddingStarData.collarSource 0 ≃ₜ
      OpenRadialInterval radius × CircleMappingTorus clutching
  monodromyCoordinates : let _ := fiberTopology
    CuspMonodromyCoordinates clutching

namespace CuspCollarRadialMappingTorusRealization

variable {A : PaperAnalyticData}
    (R : A.CuspCollarRadialMappingTorusRealization)

/-- The actual cusp collar is homotopy equivalent to its four-torus mapping torus. -/
public noncomputable def totalHomotopyEquiv :
    let _ := R.fiberTopology
    A.openEmbeddingStarData.collarSource 0 ≃ₕ CircleMappingTorus R.clutching := by
  let _ := R.fiberTopology
  exact R.totalHomeomorph.toHomotopyEquiv.trans
    (openRadialIntervalProdHomotopyEquiv R.radius_pos)

/-- The Wang calculation gives integral first-homology coordinates for the radial collar. -/
public noncomputable def homologyOneEquiv :
    IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0) ≃+
      (Fin 3 → ℤ) := by
  let _ := R.fiberTopology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 1 R.totalHomotopyEquiv).trans
    R.monodromyCoordinates.circleMappingTorusHOneAddEquiv

/-- The Wang calculation gives integral second-homology coordinates for the radial collar. -/
public noncomputable def homologyTwoEquiv :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) ≃+
      (Fin 6 → ℤ) := by
  let _ := R.fiberTopology
  exact (integralSingularHomologyEquivOfHomotopyEquiv 2 R.totalHomotopyEquiv).trans
    R.monodromyCoordinates.circleMappingTorusHTwoAddEquiv

end CuspCollarRadialMappingTorusRealization

end Geometry.PaperAnalyticData

end SphereSixComplex
