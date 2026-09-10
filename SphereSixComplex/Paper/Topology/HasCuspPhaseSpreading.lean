module

public import SphereSixComplex.Paper.Topology.EstablishedA2PhaseSpreading
public import SphereSixComplex.Paper.Geometry.CuspPuncturedCollarBridge

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.CuspStraighteningRetraction

public class HasCuspPhaseSpreading
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) : Prop where
  nonempty : Nonempty (Σ P : PolarHoneycombData M W.localWitness.radius,
    FrozenLocalCuspPhaseSpreadingData N M W.localWitness.radius P)

public def cuspPhaseSpreadingData
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) [HasCuspPhaseSpreading W] :
    Σ P : PolarHoneycombData M W.localWitness.radius,
      FrozenLocalCuspPhaseSpreadingData N M W.localWitness.radius P :=
  HasCuspPhaseSpreading.nonempty (W := W) |>.some

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
