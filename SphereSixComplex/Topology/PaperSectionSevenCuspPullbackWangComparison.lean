module

public import SphereSixComplex.Topology.PaperSectionSevenCuspCoverNaturality

/-!
# Comparing the pulled-back cusp cover with the cusp Wang coordinate

The canonical Mayer--Vietoris boundary of the pulled-back elliptic cover lands in the kernel of
the elliptic side-difference map.  This module packages that boundary as an additive homomorphism
and isolates the remaining geometric comparison with the final invariant Wang coordinate of the
actual cusp collar.  Once that single homomorphism identity is known, all six pulled-back boundary
basis calculations follow.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscHomologyCoordinates
open SectionSevenEllipticInteriorMarkedCycleData
open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.LatticeData SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.Topology.PaperCuspSpecializationAlgebra

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

/-- The pulled-back boundary as an additive homomorphism before restricting its codomain to
elliptic side-difference invariants. -/
public noncomputable def cuspPulledBackBoundaryHom :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+
      IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior) :=
  ConcreteCategory.hom
    (D.cuspOpenCoverHomologyComparison.boundary 1 ≫
      BinaryOpenCover.openIntersectionPullbackHomologyMap D.cuspToEllipticInteriorMap
        (orderThreeOpen D) (orderFourOpen D) 1 ≫
      (BinaryOpenCover.opensIntersectionHomologyIso
        (orderThreeOpen D) (orderFourOpen D) 1).inv)

public theorem cuspPulledBackBoundaryHom_apply (x) :
    D.cuspPulledBackBoundaryHom x = D.cuspPulledBackBoundary x :=
  rfl

/-- The pulled-back cusp-cover boundary, regarded as an invariant of the elliptic side
difference map. -/
public noncomputable def cuspPulledBackBoundaryInvariantHom :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+
      (presentationTwo (D := D)).Invariants where
  toFun x := ⟨D.cuspPulledBackBoundary x, by
    rw [← D.canonicalBoundary_cuspToEllipticUnionHomology x,
      ← presentationTwo_boundary]
    exact (presentationTwo (D := D)).lowDifference_boundary
      (cuspToEllipticUnionHomology D 2 x)⟩
  map_zero' := by
    apply Subtype.ext
    change D.cuspPulledBackBoundaryHom 0 = 0
    exact map_zero D.cuspPulledBackBoundaryHom
  map_add' x y := by
    apply Subtype.ext
    change D.cuspPulledBackBoundaryHom (x + y) =
      D.cuspPulledBackBoundaryHom x + D.cuspPulledBackBoundaryHom y
    exact map_add D.cuspPulledBackBoundaryHom x y

public theorem cuspPulledBackBoundaryInvariantHom_val (x) :
    (D.cuspPulledBackBoundaryInvariantHom x).1 = D.cuspPulledBackBoundary x :=
  rfl

/-- The integer coordinate of the pulled-back boundary after the elliptic intersection has been
oriented by the normalized two-disc computation. -/
public noncomputable def cuspPulledBackBoundaryCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+ ℤ :=
  N.actualHomologyCoordinates.degreeTwoInvariantEquiv.toAddEquiv.toAddMonoidHom.comp
    D.cuspPulledBackBoundaryInvariantHom

public theorem cuspPulledBackBoundaryCoordinateHom_apply
    (N : A.EllipticBandHomologyAlignment D) (x) :
    D.cuspPulledBackBoundaryCoordinateHom N x =
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
        (D.cuspPulledBackBoundaryInvariantHom x) :=
  rfl

/-- Pullback naturality identifies the new source-cover coordinate homomorphism with the
previously defined elliptic Mayer--Vietoris boundary coordinate. -/
public theorem cuspPulledBackBoundaryCoordinateHom_eq_cuspDegreeTwoBoundaryCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    D.cuspPulledBackBoundaryCoordinateHom N = cuspDegreeTwoBoundaryCoordinateHom N := by
  apply AddMonoidHom.ext
  intro x
  rw [D.cuspPulledBackBoundaryCoordinateHom_apply,
    cuspDegreeTwoBoundaryCoordinateHom_apply]
  congr 1
  apply Subtype.ext
  change D.cuspPulledBackBoundary x =
    (presentationTwo (D := D)).boundary (cuspToEllipticUnionHomology D 2 x)
  change D.cuspPulledBackBoundary x =
    canonicalBoundary D 1 (cuspToEllipticUnionHomology D 2 x)
  exact (D.canonicalBoundary_cuspToEllipticUnionHomology x).symm

/-- The second invariant coordinate of the actual radial cusp Wang boundary. -/
public noncomputable def actualCuspSecondWangBoundaryCoordinateHom (A : PaperAnalyticData) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+ ℤ := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  let totalEquiv := integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv
  let invariantEquiv :=
    (invariantsEquivOfConjugacy G.monodromyCoordinates.degreeOne.toIntLinearEquiv
      (circleMonodromyDifference G.clutching 1).toIntLinearMap mZeroDifference
      G.monodromyCoordinates.degreeOneDifference_conjugacy).trans
        mZeroInvariantsEquivIntSquared
  exact (coordinateAfterAddEquiv invariantEquiv.toAddEquiv 1).comp
    (P.totalToInvariants.toAddMonoidHom.comp totalEquiv.toAddMonoidHom)

/-- The last raw degree-two cusp coordinate is exactly the second invariant coordinate of the
geometric Wang boundary. -/
public theorem actualCuspSecondWangBoundaryCoordinateHom_eq_rawCoordinate (A : PaperAnalyticData) :
    actualCuspSecondWangBoundaryCoordinateHom A =
      coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 5 := by
  apply AddMonoidHom.ext
  intro x
  rfl

/-- The actual Wang connecting class before restricting to monodromy invariants or taking a
coordinate. -/
public noncomputable def actualCuspWangBoundary
    (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    IntegralSingularHomology 1 G.Fiber := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  exact P.boundary (integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv x)

/-- The second invariant Wang coordinate is the fourth marked fibre coordinate of the actual
Wang connecting class. -/
public theorem actualCuspSecondWangBoundaryCoordinateHom_apply_eq_fiberCoordinate
    (A : PaperAnalyticData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    actualCuspSecondWangBoundaryCoordinateHom A x =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.monodromyCoordinates.degreeOne (actualCuspWangBoundary A x) 3 := by
  rfl

/-- The elliptic invariant coordinate is the fourth marked coordinate of the boundary in the
actual band overlap. -/
public theorem cuspPulledBackBoundaryCoordinateHom_apply_eq_bandCoordinate
    (N : A.EllipticBandHomologyAlignment D)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    D.cuspPulledBackBoundaryCoordinateHom N x =
      N.actualHomologyCoordinates.bandOne (D.cuspPulledBackBoundary x) 3 := by
  rfl

/-- The smallest geometric boundary interface exposed by the current Wang API: the canonical
Mayer--Vietoris boundary and the Wang connecting class have the same fourth marked fibre
coordinate.  The Wang theorem currently exposes its connecting map only on homology, so this is
the strongest chain-comparison statement that can be formulated without choosing a chain-level
model for that theorem. -/
public structure SectionSevenCuspMarkedBoundaryComparison
    (N : A.EllipticBandHomologyAlignment D) : Prop where
  fourthCoordinate : ∀ x :
      IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0),
    N.actualHomologyCoordinates.bandOne (D.cuspPulledBackBoundary x) 3 =
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.monodromyCoordinates.degreeOne (actualCuspWangBoundary A x) 3

/-- The one remaining geometric interface: the boundary of the elliptic cover pulled back to the
actual radial cusp collar is the second invariant coordinate of its Wang boundary.  This is an
equality of homomorphisms between the two exact-sequence constructions, rather than six unrelated
basis assumptions. -/
public structure SectionSevenCuspPulledBackWangBoundaryComparison
    (N : A.EllipticBandHomologyAlignment D) : Prop where
  boundaryCoordinateHom :
    D.cuspPulledBackBoundaryCoordinateHom N =
      actualCuspSecondWangBoundaryCoordinateHom A

/-- Equality of the marked boundary coordinates is exactly the Wang comparison needed by the
Section 7 basis calculation. -/
public theorem SectionSevenCuspMarkedBoundaryComparison.toPulledBackWangBoundaryComparison
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspMarkedBoundaryComparison N) :
    D.SectionSevenCuspPulledBackWangBoundaryComparison N where
  boundaryCoordinateHom := by
    apply AddMonoidHom.ext
    intro x
    rw [D.cuspPulledBackBoundaryCoordinateHom_apply_eq_bandCoordinate,
      actualCuspSecondWangBoundaryCoordinateHom_apply_eq_fiberCoordinate]
    exact G.fourthCoordinate x

/-- Conversely, the bundled homomorphism comparison gives the marked boundary comparison. -/
public theorem SectionSevenCuspPulledBackWangBoundaryComparison.toMarkedBoundaryComparison
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackWangBoundaryComparison N) :
    D.SectionSevenCuspMarkedBoundaryComparison N where
  fourthCoordinate x := by
    rw [← D.cuspPulledBackBoundaryCoordinateHom_apply_eq_bandCoordinate,
      ← actualCuspSecondWangBoundaryCoordinateHom_apply_eq_fiberCoordinate,
      G.boundaryCoordinateHom]

/-- A comparison of the pulled-back cover boundary with the actual cusp Wang coordinate proves
all five vanishing basis calculations and the positive final boundary calculation. -/
public theorem SectionSevenCuspPulledBackWangBoundaryComparison.toPulledBackBoundaryBasisBridge
    (N : A.EllipticBandHomologyAlignment D)
    (G : D.SectionSevenCuspPulledBackWangBoundaryComparison N) :
    D.SectionSevenCuspPulledBackBoundaryBasisBridge N where
  lowerBoundary_zero i := by
    have hInvariant : D.cuspPulledBackBoundaryInvariantHom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i.castSucc 1)) = 0 := by
      apply N.actualHomologyCoordinates.degreeTwoInvariantEquiv.injective
      rw [map_zero]
      change D.cuspPulledBackBoundaryCoordinateHom N
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i.castSucc 1)) = 0
      rw [G.boundaryCoordinateHom,
        actualCuspSecondWangBoundaryCoordinateHom_eq_rawCoordinate,
        coordinateAfterAddEquiv_apply,
        AddEquiv.apply_symm_apply]
      rw [show (5 : Fin 6) = Fin.last 5 by rfl,
        Pi.single_eq_of_ne (Fin.castSucc_ne_last i).symm]
    exact congrArg Subtype.val hInvariant
  e5_boundary := by
    have hInvariant : D.cuspPulledBackBoundaryInvariantHom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) =
          N.actualHomologyCoordinates.degreeTwoInvariantEquiv.symm 1 := by
      apply N.actualHomologyCoordinates.degreeTwoInvariantEquiv.injective
      change D.cuspPulledBackBoundaryCoordinateHom N
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) =
        N.actualHomologyCoordinates.degreeTwoInvariantEquiv
          (N.actualHomologyCoordinates.degreeTwoInvariantEquiv.symm 1)
      rw [G.boundaryCoordinateHom,
        actualCuspSecondWangBoundaryCoordinateHom_eq_rawCoordinate,
        coordinateAfterAddEquiv_apply,
        AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      simp
    exact congrArg Subtype.val hInvariant

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
