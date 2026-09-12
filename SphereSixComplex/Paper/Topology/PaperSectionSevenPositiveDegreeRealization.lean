module

public import SphereSixComplex.Paper.Topology.PaperEllipticInteriorNormalizedSplitting
public import SphereSixComplex.Paper.Topology.PaperCuspCollarRadialMappingTorus
public import SphereSixComplex.Paper.Topology.PaperEllipticTwoDiscHomologyCoordinatesRealization
public import SphereSixComplex.Paper.Topology.PaperCuspCentralFiberHomology
public import SphereSixComplex.Paper.Topology.PaperCuspPhaseSpreading
public import SphereSixComplex.Paper.Topology.PaperSectionSevenFinalDegreeZero
public import SphereSixComplex.Paper.Topology.PaperSectionSevenEllipticTwoDiscCoverRealization

/-!
# Coordinate homomorphisms for the cusp boundary

Coordinate evaluation after an additive lattice equivalence gives additive homomorphisms.
The cusp boundary coordinate is the actual Wang boundary followed by its marked invariant
coordinate. The evaluation formula is proved here.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set

namespace SphereSixComplex


namespace Geometry.AnalyticData

open EllipticTwoDiscHomologyCoordinates

variable {A : AnalyticData}


namespace EllipticInteriorMarkedCycleData

variable {D : A.EllipticTwoDiscCoverData}


/-- Evaluate one coordinate after an additive equivalence to a finite integer lattice. -/
public def coordinateAfterAddEquiv {G : Type*} [AddCommGroup G] {n : ℕ}
    (e : G ≃+ (Fin n → ℤ)) (i : Fin n) : G →+ ℤ where
  toFun x := e x i
  map_zero' := by simp
  map_add' x y := by simp


/-- The invariant boundary coordinate of an included cusp degree-two class. -/
public noncomputable def cuspDegreeTwoBoundaryCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+ ℤ where
  toFun x := N.actualHomologyCoordinates.degreeTwoInvariantEquiv
    ((presentationTwo (D := D)).totalToInvariants (cuspToEllipticUnionHomology D 2 x))
  map_zero' := by
    change N.actualHomologyCoordinates.degreeTwoInvariantEquiv
      ((presentationTwo (D := D)).totalToInvariants
        (cuspToEllipticUnionHomology D 2 0)) = 0
    rw [show cuspToEllipticUnionHomology D 2 0 = 0 by
      simp [cuspToEllipticUnionHomology], map_zero, map_zero]
  map_add' x y := by
    change N.actualHomologyCoordinates.degreeTwoInvariantEquiv
        ((presentationTwo (D := D)).totalToInvariants
          (cuspToEllipticUnionHomology D 2 (x + y))) = _
    rw [show cuspToEllipticUnionHomology D 2 (x + y) =
        cuspToEllipticUnionHomology D 2 x + cuspToEllipticUnionHomology D 2 y by
      simp [cuspToEllipticUnionHomology], map_add, map_add]

public theorem cuspDegreeTwoBoundaryCoordinateHom_apply
    (N : A.EllipticBandHomologyAlignment D) (x) :
    cuspDegreeTwoBoundaryCoordinateHom N x =
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
      ((presentationTwo (D := D)).totalToInvariants
        (cuspToEllipticUnionHomology D 2 x)) := rfl


end EllipticInteriorMarkedCycleData


end Geometry.AnalyticData

end SphereSixComplex
