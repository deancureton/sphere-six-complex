module

public import SphereSixComplex.Topology.PaperSectionSevenPositiveDegreeRealization

/-!
# Removing the redundant cusp fibre-basis check

The positive cusp `e₅` class defines the normalized swept-cycle splitting.  Consequently its
fibre coordinate is zero by construction, so that basis-vector check need not be supplied again.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData} {D : A.SectionSevenEllipticTwoDiscCoverData}

/-- The cusp `e₅` generator has zero fibre coordinate in the splitting that it defines. -/
public theorem degreeTwoCuspE5_fiberCoordinate_zero
    (N : A.EllipticBandHomologyAlignment D)
    (hBoundary : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2 x)) =
        A.actualCuspRawHomologyTwoEquiv x 5) :
    N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
        (N.actualHomologyCoordinates.degreeTwoCuspE5SplittingOfCoordinates hBoundary)
        (degreeTwoCuspE5Generator (A := A) (D := D)) 0 = 0 := by
  let B := N.actualHomologyCoordinates
  let S := B.degreeTwoCuspE5SplittingOfCoordinates hBoundary
  have hg : degreeTwoCuspE5Generator (A := A) (D := D) =
      S.sweptSection ((B.degreeTwoInvariantEquiv).symm 1) := by
    dsimp [S, degreeTwoCuspE5SplittingOfCoordinates, degreeTwoSplittingOfCuspE5,
      degreeTwoSplittingOfGenerator]
    change degreeTwoCuspE5Generator (A := A) (D := D) =
      B.degreeTwoInvariantEquiv (B.degreeTwoInvariantEquiv.symm 1) •
        degreeTwoCuspE5Generator (A := A) (D := D)
    rw [LinearEquiv.apply_symm_apply]
    simp
  rw [hg]
  have h := congrFun (B.normalizedUnionHomologyTwoEquiv_add S 0
    (B.degreeTwoInvariantEquiv.symm 1)) (0 : Fin 2)
  simpa using h

namespace SectionSevenEllipticInteriorMarkedCycleData

/-- Build the marked-cycle package without rechecking the `e₅` fibre coordinate.  That
coordinate vanishes because `e₅` is the swept-cycle generator used to define the splitting. -/
public noncomputable def ofCuspBoundaryBasisCoordinatesExceptE5Fiber
    (N : A.EllipticBandHomologyAlignment D)
    (hOneBasis : ∀ i : Fin 3,
      N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
          (cuspToEllipticUnionHomology D 1
            (A.actualCuspRawHomologyOneEquiv.symm (Pi.single i 1))) 0 =
        (Pi.single i 1 : Fin 3 → ℤ) 2)
    (hBoundaryBasis : ∀ i : Fin 6,
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2
              (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)))) =
        (Pi.single i 1 : Fin 6 → ℤ) 5)
    (hTwoZeroBasis : ∀ i : Fin 6, i ≠ 5 →
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
          (N.actualHomologyCoordinates.degreeTwoCuspE5SplittingOfCoordinates
            (degreeTwoCuspBoundaryCoordinates_of_basis N hBoundaryBasis))
          (cuspToEllipticUnionHomology D 2
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) 0 =
        (Pi.single i 1 : Fin 6 → ℤ) 4) :
    A.SectionSevenEllipticInteriorMarkedCycleData D := by
  apply SectionSevenEllipticInteriorMarkedCycleData.ofCuspBoundaryBasisCoordinates
    N hOneBasis hBoundaryBasis
  intro i
  by_cases hi : i = 5
  · subst i
    simpa [degreeTwoCuspE5Generator] using
      degreeTwoCuspE5_fiberCoordinate_zero N
        (degreeTwoCuspBoundaryCoordinates_of_basis N hBoundaryBasis)
  · exact hTwoZeroBasis i hi

end SectionSevenEllipticInteriorMarkedCycleData

end SphereSixComplex.Geometry.PaperAnalyticData
