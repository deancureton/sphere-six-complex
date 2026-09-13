module

public import SphereSixComplex.Paper.Topology.PaperEllipticTorusHomologyBasis
public import SphereSixComplex.Paper.Topology.PaperLemmaSevenThirteenAlgebra

public import SphereSixComplex.Paper.Topology.PaperMultipleFiberHOneTopologyDerived

/-!
# Homology coordinates for affine cyclic torus quotients

The canonical order-three and order-four lattice maps are written in their presentation
coordinates. The source of an affine cyclic central-fibre cover receives its homology basis
from the standard torus through the actual source homeomorphism.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix

namespace SphereSixComplex.AffineCyclicQuotientHomology

open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticFamilySpecialization Geometry.GlobalTorusFamily
open LatticeData EllipticFilling
open EllipticFilling MultipleFiberCoinvariants
open AffineCyclicQuotientHomology
open SphereSixComplex.Topology.TwistObstruction

/-- Coordinates of the canonical order-three lattice-to-presentation map. -/
public def orderThreeLatticeProjectionCoordinates : Lattice →+ IntSquared where
  toFun x := ![3 * gamma x, psiOne x]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    ring

/-- Coordinates of the canonical order-four lattice-to-presentation map. -/
public def orderFourLatticeProjectionCoordinates : Lattice →+ IntSquared where
  toFun x := ![4 * gamma x, psiTwo x]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    ring

variable {m : ℕ} [NeZero m] {p : SphereSixComplex.Periods.Parameters}
  {D : RadialEllipticActionData m (AdditiveTorus p)}

/-- The standard homology basis on the source of an affine cyclic central-fibre cover. -/
public def affineCyclicCentralFiberCoverSourceHomologyBasis
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    FourTorusHomologyBasis (RadialEllipticActionData.CentralFiberCoverSource D) :=
  (StandardTorusHomology.additiveTorusHomologyBasis p P.fullRank).homeomorph
    (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D)

variable {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)

end SphereSixComplex.AffineCyclicQuotientHomology
