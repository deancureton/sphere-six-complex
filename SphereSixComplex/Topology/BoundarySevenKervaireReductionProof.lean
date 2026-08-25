module

public import SphereSixComplex.Topology.BoundarySevenCechTotalQuasiIsoProof
public import SphereSixComplex.Topology.BoundarySevenDegreeTransportProof
public import SphereSixComplex.Topology.GeometricThetaSixUnconditionalEndpoint
public import SphereSixComplex.Topology.KervaireInvariantGeometricSix

/-!
# The remaining geometric reduction for `Theta₆`

The boundary-seven Cech comparison computes the middle mod-two homology of the standard
six-sphere.  Consequently the geometric Kervaire invariant of every stable framing vanishes,
and the Kervaire--Pontryagin--Thom detection statement alone supplies the parallelizable
fillings required by the geometric endpoint.

This file records the resulting sharp boundary of the formalization.  It does not assume or
claim the remaining stable-framing, detection, surgery, or puncturing theorems.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

namespace OrientedMarkedSmoothHomotopySixSphere

/-- The proved mod-two computation reduces the parallelizable-filling obligation to the
Kervaire--Pontryagin--Thom detection theorem alone. -/
public theorem stableFramingsBoundParallelizableSevenManifolds_of_kervaireDetection_proof
    (hDetection : StableFramedSixSphereKervairePTDetection) :
    StableFramingsBoundParallelizableSevenManifolds :=
  stableFramingsBoundParallelizableSevenManifolds_of_standard_modTwoH₃
    sixSphere_modTwoHomology_three_isZero_proof hDetection

/-- A degree theory furnished by the completed integral simplicial-to-singular comparison. -/
public noncomputable def constructedSixSphereDegreeTheory : SixSphereDegreeTheory :=
  Classical.choice
    (sixSphereDegreeTheory_of_boundarySevenComparison
      boundarySeven_integralComparison_proof)

/-- The completed homology calculation reduces the genuine one-step geometric `Theta₆`
endpoint to the four remaining geometric and stable-homotopy inputs. -/
public theorem constructedDegree_unconditionalGeometricThetaSixVanishes_of_remaining_inputs
    (hStable : HomotopySixSpheresStablyParallelizable)
    (hDetection : StableFramedSixSphereKervairePTDetection)
    (hSurgery : ParallelizableFillingSurgeryToContractible)
    (hPuncture :
      ContractibleFillingPuncturesToHCobordism constructedSixSphereDegreeTheory) :
    (unconditionalGeometricSmoothHCobordismRelation
      constructedSixSphereDegreeTheory).ThetaSixVanishes :=
  unconditionalGeometricThetaSixVanishes_of_framedBordism_and_surgery
    constructedSixSphereDegreeTheory hStable
    (stableFramingsBoundParallelizableSevenManifolds_of_kervaireDetection_proof
      hDetection)
    hSurgery hPuncture

/-- The same four-input reduction, transported to the repository's public compatibility
quotient endpoint. -/
public theorem
    constructedDegree_unconditionalGeometricThetaSixVanishesAdapter_of_remaining_inputs
    (hStable : HomotopySixSpheresStablyParallelizable)
    (hDetection : StableFramedSixSphereKervairePTDetection)
    (hSurgery : ParallelizableFillingSurgeryToContractible)
    (hPuncture :
      ContractibleFillingPuncturesToHCobordism constructedSixSphereDegreeTheory) :
    SmoothHCobordismRelation.ThetaSixVanishes
      (unconditionalGeometricSmoothHCobordismRelation
        constructedSixSphereDegreeTheory).toSmoothHCobordismRelation :=
  unconditionalGeometricThetaSixVanishesAdapter_of_framedBordism_and_surgery
    constructedSixSphereDegreeTheory hStable
    (stableFramingsBoundParallelizableSevenManifolds_of_kervaireDetection_proof
      hDetection)
    hSurgery hPuncture

end OrientedMarkedSmoothHomotopySixSphere

end SphereSixComplex
