module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction
public import SphereSixComplex.Paper.Geometry.CuspCollarPairProperness
public import SphereSixComplex.Paper.Geometry.RealPeriodTrivialization
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryUniversalCover

/-!
# The canonical map from the cusp fibre to the elliptic band

The actual cusp clutching identifies its fibre with a full-rank period torus.  Real-period
coordinates canonically identify that torus with the selected torus of the central elliptic
band, and the inverse band trivialization includes it into the actual band overlap.  This gives
a genuine continuous map whose homology map is the comparison map required by the final Wang
square.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.EllipticFilling


/-- The chosen radial clutching coordinates carry their defining period marking. -/
public theorem cuspFiberPeriodMarkingCompatibility (A : AnalyticData) :
    (let G := A.actualCuspRadialClutchingData
       let _ := G.fiberTopology
       ∀ x : IntegralSingularHomology 1 G.Fiber,
         (StandardTorusHomology.additiveTorusHomologyBasis
             G.fiberParameter G.fiberFullRank).degreeOne
             (integralSingularHomologyMap 1 G.fiberHomeomorph x) =
           G.monodromyCoordinates.degreeOne x) :=
  A.actualCuspRadialClutchingData.fiberMarkingCompatibility

variable {A : AnalyticData} (D : A.EllipticTwoDiscCoverData)

namespace EllipticTwoDiscCoverData

/-- Real-period coordinates identify the actual cusp fibre with the torus selected by the
elliptic band. -/
public noncomputable def canonicalCuspFiberToBandTorusHomeomorph :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.Fiber ≃ₜ AdditiveTorus D.bandParameter := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact G.fiberHomeomorph.trans
    (fullRankAdditiveTorusHomeomorph G.fiberParameter D.bandParameter
      G.fiberFullRank D.bandFullRank)

/-- The actual continuous map from the cusp Wang fibre to the central band overlap. -/
public noncomputable def canonicalCuspFiberToBandMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber,
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact D.bandHomotopyEquiv.invFun.comp
    ⟨D.canonicalCuspFiberToBandTorusHomeomorph,
      D.canonicalCuspFiberToBandTorusHomeomorph.continuous⟩

/-- The homology map induced by the real-period homeomorphism from the cusp fibre to the band
torus. -/
public noncomputable def canonicalCuspFiberToBandTorusHomologyOne :
    (let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) →+
      IntegralSingularHomology 1 (AdditiveTorus D.bandParameter) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact integralSingularHomologyMap 1 D.canonicalCuspFiberToBandTorusHomeomorph

/-- The homology map induced by the canonical geometric cusp-fibre-to-band map. -/
public noncomputable def canonicalCuspFiberToBandHomologyOne :
    (let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) →+
      IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact integralSingularHomologyMap 1 D.canonicalCuspFiberToBandMap

/-- Applying the selected band equivalence cancels the inverse band trivialization in the
canonical geometric map. -/
public theorem bandHomologyEquiv_canonicalCuspFiberToBandHomologyOne
    (x : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber) :
    D.bandHomologyEquiv 1 (D.canonicalCuspFiberToBandHomologyOne x) =
      (let G := A.actualCuspRadialClutchingData
       let _ := G.fiberTopology
       D.canonicalCuspFiberToBandTorusHomologyOne x) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [show D.canonicalCuspFiberToBandHomologyOne x =
      integralSingularHomologyMap 1 D.canonicalCuspFiberToBandMap x by rfl]
  rw [show integralSingularHomologyMap 1 D.canonicalCuspFiberToBandMap =
      (integralSingularHomologyMap 1 D.bandHomotopyEquiv.invFun).comp
        (integralSingularHomologyMap 1
          D.canonicalCuspFiberToBandTorusHomeomorph) by
    exact integralSingularHomologyMap_comp 1 _ _]
  exact (integralSingularHomologyEquivOfHomotopyEquiv 1
    D.bandHomotopyEquiv).apply_symm_apply _




theorem actualHomologyCoordinates_bandOne_apply
    (N : A.EllipticBandHomologyAlignment D)
    (x : IntegralSingularHomology 1
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :
    N.actualHomologyCoordinates.bandOne x =
      EllipticBandHomologyAlignment.bandOne (D := D) x := by
  rfl

/-- The order-three period-marking comparison implies naturality of the complete marking on the
actual band. -/
public theorem canonicalCuspFiberBandPeriodMarking_of_orderThree
    (N : A.EllipticBandHomologyAlignment D)
    (h : (let G := A.actualCuspRadialClutchingData
            let _ := G.fiberTopology
            ∀ x : IntegralSingularHomology 1 G.Fiber,
              (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
                  (integralSingularHomologyMap 1 D.bandToOrderThreeCoverSource
                    (D.canonicalCuspFiberToBandTorusHomologyOne x)) =
                G.monodromyCoordinates.degreeOne x)) :
    (N.actualHomologyCoordinates.bandOne.toAddMonoidHom.comp
           D.canonicalCuspFiberToBandHomologyOne =
         let G := A.actualCuspRadialClutchingData
         let _ := G.fiberTopology
         G.monodromyCoordinates.degreeOne.toAddMonoidHom) := by
  apply AddMonoidHom.ext
  intro x
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  change N.actualHomologyCoordinates.bandOne
      (D.canonicalCuspFiberToBandHomologyOne x) =
    G.monodromyCoordinates.degreeOne x
  rw [D.actualHomologyCoordinates_bandOne_apply]
  rw [EllipticBandHomologyAlignment.bandOne_apply]
  rw [D.bandHomologyEquiv_canonicalCuspFiberToBandHomologyOne]
  exact h x


end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.AnalyticData
