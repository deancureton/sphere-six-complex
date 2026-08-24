module

public import SphereSixComplex.Topology.EstablishedA2PhaseSpreading

/-!
# The phase-spread retraction for the paper cusp

The standard infinite-`A₂` compatibility package supplies the phase-spread frozen retraction,
which Lemma 7.5 transports to the actual cusp action.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

variable (A : PaperAnalyticData)

/-- The jointly selected positive-part and phase-spreading package for the paper cusp. -/
public noncomputable def cuspPhaseSpreadingPackage :
    Σ P : PolarHoneycombData A.toricModel A.starCuspWitness.localWitness.radius,
      FrozenLocalCuspPhaseSpreadingData A.cuspCoordinate A.toricModel
        A.starCuspWitness.localWitness.radius P :=
  Classical.choice (Established.polarHoneycombPhaseSpreadingPackage
    A.cuspCoordinate A.toricModel A.starCuspWitness.localWitness.radius
      A.starCuspWitness.localWitness.radius_pos)

/-- The unconditional actual central-fibre retraction datum for the cusp selected by `A`. -/
public noncomputable def cuspCentralFiberRetractionData :
    ActualLocalCuspCentralFiberRetractionData A.starCuspWitness :=
  actualLocalCuspCentralFiberRetractionData A.starCuspWitness
    A.cuspPhaseSpreadingPackage.1 A.cuspPhaseSpreadingPackage.2

/-- The actual central-fibre retraction for the globally selected analytic package. -/
public noncomputable def selectedCuspCentralFiberRetractionData :
    ActualLocalCuspCentralFiberRetractionData paperAnalyticData.starCuspWitness :=
  paperAnalyticData.cuspCentralFiberRetractionData

end SphereSixComplex.Geometry.PaperAnalyticData
