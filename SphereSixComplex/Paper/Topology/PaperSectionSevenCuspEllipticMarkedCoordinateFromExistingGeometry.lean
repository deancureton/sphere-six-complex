module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction
public import SphereSixComplex.Paper.Geometry.CuspCollarPairProperness
public import SphereSixComplex.Paper.Geometry.RealPeriodTrivialization
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryUniversalCover
public import SphereSixComplex.Prerequisites.Topology.MayerVietoris
public import Mathlib.Algebra.Category.Grp.EpiMono

public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecializationProof

/-!
# Coordinates of the included elliptic band

The canonical band inclusion maps fiber homology into the Wang coinvariant summand. The
normalized union coordinates identify this actual map with the marked coinvariant coordinates.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.LatticeData
open SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.CuspMonodromyCoinvariants
open EllipticTwoDiscHomologyCoordinates
open EllipticTwoDiscCoverData

variable {A : AnalyticData} (D : A.EllipticTwoDiscCoverData)

namespace EllipticTwoDiscCoverData

public def canonicalBandToEllipticInteriorInclusionMap :
    C((D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior),
      A.ellipticInterior) :=
  ⟨Subtype.val, continuous_subtype_val⟩

end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.AnalyticData

end
