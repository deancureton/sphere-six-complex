module

public import SphereSixComplex.Topology.PaperCuspFiniteFiberDegreeTwoMarkedImagesProof

/-!
# Pointwise specialization of the retained degree-two coordinate tori
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.StandardTorusHomology

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
  {W : ActualPuncturedCuspCollarWitness N M}

namespace CuspFiberSpecializationNormalization

/-- A chosen vector representative of a point on one of the four retained coordinate tori. -/
public noncomputable def degreeTwoMarkedFiberCoordinateVector
    (G : ActualCuspRadialClutchingData W) (j : Fin 4)
    (z : StandardTorusHomology.StdTorus 2) : ComplexTwoSpace :=
  Quotient.out
    ((StandardTorusHomology.additiveTorusStdHomeomorph
      G.fiberParameter G.fiberFullRank).symm
        (standardFourTorusCoordinateTwoTorus (degreeTwoMarkedPairIndex j) z))

public theorem additiveTorusProjection_degreeTwoMarkedFiberCoordinateVector
    (G : ActualCuspRadialClutchingData W) (j : Fin 4)
    (z : StandardTorusHomology.StdTorus 2) :
    additiveTorusProjection G.fiberParameter
        (degreeTwoMarkedFiberCoordinateVector G j z) =
      (StandardTorusHomology.additiveTorusStdHomeomorph
        G.fiberParameter G.fiberFullRank).symm
          (standardFourTorusCoordinateTwoTorus (degreeTwoMarkedPairIndex j) z) :=
  Quotient.out_eq _

/-- The actual specialization of each retained coordinate torus is pointwise the normalized
additive-period point used to define the cusp collar. -/
public theorem markedFiberToCuspFilling_degreeTwoMarkedFiberCoordinateTorus_apply
    (G : ActualCuspRadialClutchingData W) (j : Fin 4)
    (z : StandardTorusHomology.StdTorus 2) :
    let _ := G.fiberTopology
    G.markedFiberToCuspFilling (degreeTwoMarkedFiberCoordinateTorus G j z) =
      puncturedLocalCuspToFilling W
        (actualCuspCollarPeriodPoint W G.markingParameter_mem
          (degreeTwoMarkedFiberCoordinateVector G j z)) := by
  let _ := G.fiberTopology
  apply G.markedFiberToCuspFilling_eq_actualCuspCollarPeriodPoint
  change G.fiberHomeomorph
      (G.fiberHomeomorph.symm
        ((StandardTorusHomology.additiveTorusStdHomeomorph
          G.fiberParameter G.fiberFullRank).symm
            (standardFourTorusCoordinateTwoTorus (degreeTwoMarkedPairIndex j) z))) = _
  rw [G.fiberHomeomorph.apply_symm_apply]
  exact additiveTorusProjection_degreeTwoMarkedFiberCoordinateVector G j z |>.symm

end CuspFiberSpecializationNormalization

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge

end
