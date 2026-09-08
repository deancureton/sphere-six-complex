module
public import SphereSixComplex.Topology.CuspFourthActionSweep
public import SphereSixComplex.Topology.EllipticFourthFiberSweep
public import SphereSixComplex.Topology.CuspCorrectedEllipticSplitting

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData

public theorem cuspEllipticFiberCoordinate_rawFive (A : PaperAnalyticData)
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := R.twoDiscCover))) :
    A.cuspEllipticFiberCoordinate R S
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) = 1 := by
  let f := coordinateAfterAddEquiv
    (R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv S) 0
  have h := congrArg f A.ellipticFourthHomologySweep_fullIterate
  rw [A.ellipticFourthHomologySweep_cusp R.twoDiscCover, map_zsmul, map_neg] at h
  have hf := A.ellipticFourthSweep_translation_fiberCoordinate R S
  change f (A.ellipticFourthHomologySweep _) = -12 at hf
  rw [hf] at h
  change (12 : ℤ) • (-A.cuspEllipticFiberCoordinate R S
    (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) = -12 at h
  change (12 : ℤ) * (-A.cuspEllipticFiberCoordinate R S
    (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) = -12 at h
  omega

end SphereSixComplex.Geometry.PaperAnalyticData
