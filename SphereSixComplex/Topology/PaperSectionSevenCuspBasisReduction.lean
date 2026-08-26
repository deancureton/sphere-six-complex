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

/-- A geometric Mayer--Vietoris comparison for the degree-two cusp basis.  The first five raw
basis classes lift to the homology of the two elliptic sides, while the final suspension class
has the chosen positive boundary. -/
public structure SectionSevenCuspDegreeTwoMayerVietorisBasisBridge
    (N : A.EllipticBandHomologyAlignment D) : Prop where
  lowerBasis_factors : ∀ i : Fin 5, ∃ y :
      IntegralSingularHomology 2 D.orderThreeSide ×
        IntegralSingularHomology 2 D.orderFourSide,
    (presentationTwo (D := D)).inclusion y =
      cuspToEllipticUnionHomology D 2
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i.castSucc 1))
  e5_boundary :
    (presentationTwo (D := D)).totalToInvariants
        (degreeTwoCuspE5Generator (A := A) (D := D)) =
      (N.actualHomologyCoordinates.degreeTwoInvariantEquiv).symm 1

/-- Factoring the five fibre classes through the side homology kills their connecting-map
coordinate; the bridge's orientation condition supplies the remaining `e₅` coordinate. -/
public theorem SectionSevenCuspDegreeTwoMayerVietorisBasisBridge.boundaryCoordinates
    (N : A.EllipticBandHomologyAlignment D)
    (G : A.SectionSevenCuspDegreeTwoMayerVietorisBasisBridge N) (i : Fin 6) :
    N.actualHomologyCoordinates.degreeTwoInvariantEquiv
        ((presentationTwo (D := D)).totalToInvariants
          (cuspToEllipticUnionHomology D 2
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)))) =
      (Pi.single i 1 : Fin 6 → ℤ) 5 := by
  by_cases hi : i = 5
  · subst i
    have h := congrArg N.actualHomologyCoordinates.degreeTwoInvariantEquiv G.e5_boundary
    rw [LinearEquiv.apply_symm_apply] at h
    simpa [degreeTwoCuspE5Generator] using h
  · have hi_val : i.val ≠ 5 := fun h ↦ hi (Fin.ext h)
    have hil : i.val < 5 := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hi_val
    let j : Fin 5 := ⟨i, hil⟩
    obtain ⟨y, hy⟩ := G.lowerBasis_factors j
    have hji : j.castSucc = i := Fin.ext rfl
    rw [← hji, ← hy]
    have hzero : (presentationTwo (D := D)).totalToInvariants
        ((presentationTwo (D := D)).inclusion y) = 0 := by
      apply Subtype.ext
      exact (presentationTwo (D := D)).boundary_inclusion y
    rw [hzero, map_zero]
    rw [show (5 : Fin 6) = Fin.last 5 by rfl,
      Pi.single_eq_of_ne (Fin.castSucc_ne_last j).symm]

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

/-- Build the marked-cycle package from a geometric Mayer--Vietoris basis bridge.  This replaces
six scalar boundary checks by five side-factorizations and the orientation of the final
suspension class. -/
public noncomputable def ofCuspMayerVietorisBasisBridge
    (N : A.EllipticBandHomologyAlignment D)
    (G : A.SectionSevenCuspDegreeTwoMayerVietorisBasisBridge N)
    (hOneBasis : ∀ i : Fin 3,
      N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
          (cuspToEllipticUnionHomology D 1
            (A.actualCuspRawHomologyOneEquiv.symm (Pi.single i 1))) 0 =
        (Pi.single i 1 : Fin 3 → ℤ) 2)
    (hTwoZeroBasis : ∀ i : Fin 6, i ≠ 5 →
      N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv
          (N.actualHomologyCoordinates.degreeTwoCuspE5SplittingOfCoordinates
            (degreeTwoCuspBoundaryCoordinates_of_basis N
              (fun i ↦ G.boundaryCoordinates N i)))
          (cuspToEllipticUnionHomology D 2
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) 0 =
        (Pi.single i 1 : Fin 6 → ℤ) 4) :
    A.SectionSevenEllipticInteriorMarkedCycleData D :=
  ofCuspBoundaryBasisCoordinatesExceptE5Fiber N hOneBasis
    (fun i ↦ G.boundaryCoordinates N i) hTwoZeroBasis

end SectionSevenEllipticInteriorMarkedCycleData

end SphereSixComplex.Geometry.PaperAnalyticData
