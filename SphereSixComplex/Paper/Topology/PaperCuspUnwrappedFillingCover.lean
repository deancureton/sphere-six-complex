module

public import SphereSixComplex.Paper.Topology.PaperCuspFillingDeckAction

/-!
# A representative of the cusp boundary basepoint

Choose an additive cusp-boundary representative and record its image under the quotient map.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry Geometry.ComplexTorus Geometry.CuspCollar
open Geometry.InfiniteA2Toric

namespace Geometry.CuspCollar

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
variable {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- A selected preimage in the normalized additive cover of a prescribed boundary base point. -/
public noncomputable def paperCuspBoundaryBasePreimage
    (W : ActualPuncturedCuspCollarWitness N M) (b : PuncturedLocalCuspQuotient W) :
    additiveCuspRadiusCover W.localWitness.radius := by
  let _ := paperCuspBoundaryDeckAction W
  exact Classical.choose
    ((additiveCuspBoundaryProjection_isQuotientCoveringMap W).surjective b)

@[simp]
public theorem additiveCuspBoundaryProjection_basePreimage
    (W : ActualPuncturedCuspCollarWitness N M) (b : PuncturedLocalCuspQuotient W) :
    additiveCuspBoundaryProjection W (paperCuspBoundaryBasePreimage W b) = b := by
  let _ := paperCuspBoundaryDeckAction W
  exact Classical.choose_spec
    ((additiveCuspBoundaryProjection_isQuotientCoveringMap W).surjective b)


end Geometry.CuspCollar

end SphereSixComplex

end
