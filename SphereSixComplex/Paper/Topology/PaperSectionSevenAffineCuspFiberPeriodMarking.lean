module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCanonicalCuspFiberBandMap

/-!
# Period marking for the affine cusp-to-band map

For the affine radial cover, the selected band torus is the order-three period torus and the map
to the order-three cover source is the inverse of its standard homeomorphism.  The full period
marking therefore follows from the cusp fibre marking and cross-parameter naturality of the
standard torus homology basis.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex

open SphereSixComplex.Geometry SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup
open EllipticFilling

private theorem orderThreeCoverSourceDegreeOne_symm
    {U : SphereSixComplex.Periods.TriangleUniformization} (F : PeriodFunctions U)
    (z : IntegralSingularHomology 1 (AdditiveTorus (parameterMap F U.zOne).1)) :
    (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne
        (integralSingularHomologyMap 1
          (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderThreeRadialActionData F)).symm z) =
      (orderThreeTorusHomologyBasis F).degreeOne z := by
  let e := RadialEllipticActionData.centralFiberCoverSourceHomeomorph
    (orderThreeRadialActionData F)
  have h := (integralSingularHomologyEquiv 1 e).apply_symm_apply z
  exact congrArg (orderThreeTorusHomologyBasis F).degreeOne h

private noncomputable def actualCuspFiberToPeriodTorusHomologyOne
    (A : Geometry.AnalyticData) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1 G.Fiber →+
      IntegralSingularHomology 1 (AdditiveTorus G.fiberParameter) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact integralSingularHomologyMap 1 G.fiberHomeomorph

private theorem canonicalCuspFiberToBandTorusHomologyOne_eq_comp
    {A : Geometry.AnalyticData}
    (D : A.EllipticTwoDiscCoverData) :
    D.canonicalCuspFiberToBandTorusHomologyOne =
      (integralSingularHomologyMap 1
        (Geometry.AnalyticData.fullRankAdditiveTorusHomeomorph
          A.actualCuspRadialClutchingData.fiberParameter D.bandParameter
          A.actualCuspRadialClutchingData.fiberFullRank D.bandFullRank)).comp
        (actualCuspFiberToPeriodTorusHomologyOne A) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let e := Geometry.AnalyticData.fullRankAdditiveTorusHomeomorph
    G.fiberParameter D.bandParameter G.fiberFullRank D.bandFullRank
  exact integralSingularHomologyMap_comp 1
    ⟨G.fiberHomeomorph, G.fiberHomeomorph.continuous⟩ ⟨e, e.continuous⟩

namespace Geometry.AnalyticData

variable {A : AnalyticData}

private theorem affineTwoDiscCover_degreeOneBasis
    (R : A.AffineRadialCompletionInput)
    (z : IntegralSingularHomology 1 (AdditiveTorus R.twoDiscCover.bandParameter)) :
    (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
        (integralSingularHomologyMap 1 R.twoDiscCover.bandToOrderThreeCoverSource z) =
      (StandardTorusHomology.additiveTorusHomologyBasis
        R.twoDiscCover.bandParameter R.twoDiscCover.bandFullRank).degreeOne z := by
  exact orderThreeCoverSourceDegreeOne_symm A.periods z

/-- Compatibility of the actual cusp fibre marking implies the complete order-three period
marking for the canonical map into the affine elliptic band. -/
public theorem AffineRadialCompletionInput.canonicalCuspFiberOrderThreePeriodMarking
    (R : A.AffineRadialCompletionInput)
    (hCusp : (let G := A.actualCuspRadialClutchingData
                let _ := G.fiberTopology
                ∀ x : IntegralSingularHomology 1 G.Fiber,
                  (StandardTorusHomology.additiveTorusHomologyBasis
                      G.fiberParameter G.fiberFullRank).degreeOne
                      (integralSingularHomologyMap 1 G.fiberHomeomorph x) =
                    G.monodromyCoordinates.degreeOne x)) :
    (let G := A.actualCuspRadialClutchingData
       let _ := G.fiberTopology
       ∀ x : IntegralSingularHomology 1 G.Fiber,
         (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
             (integralSingularHomologyMap 1 R.twoDiscCover.bandToOrderThreeCoverSource
               (R.twoDiscCover.canonicalCuspFiberToBandTorusHomologyOne x)) =
           G.monodromyCoordinates.degreeOne x) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  dsimp only
  intro x
  let y := actualCuspFiberToPeriodTorusHomologyOne A x
  let e := fullRankAdditiveTorusHomeomorph
    G.fiberParameter R.twoDiscCover.bandParameter
    G.fiberFullRank R.twoDiscCover.bandFullRank
  have hNatural :=
    (StandardTorusHomology.fullRankAdditiveTorusHomeomorph_naturality
      G.fiberParameter R.twoDiscCover.bandParameter
      G.fiberFullRank R.twoDiscCover.bandFullRank).1 y
  have hComposite :
      R.twoDiscCover.canonicalCuspFiberToBandTorusHomologyOne x =
        integralSingularHomologyMap 1 e y := by
    exact DFunLike.congr_fun
      (canonicalCuspFiberToBandTorusHomologyOne_eq_comp R.twoDiscCover) x
  rw [hComposite]
  calc
    _ = (StandardTorusHomology.additiveTorusHomologyBasis
          R.twoDiscCover.bandParameter R.twoDiscCover.bandFullRank).degreeOne
        (integralSingularHomologyMap 1 e y) := by
      exact affineTwoDiscCover_degreeOneBasis R _
    _ = G.monodromyCoordinates.degreeOne x := hNatural.trans (hCusp x)

end Geometry.AnalyticData

end SphereSixComplex
