module

public import SphereSixComplex.Topology.NormalizedWangHomologySplitting
public import SphereSixComplex.Topology.PaperCuspGeometricSpecialization
public import SphereSixComplex.Topology.PaperEllipticTwoDiscHomologyCoordinatesRealization

/-!
# Swept-cycle normalization for the elliptic interior

The rank-two Mayer--Vietoris computation splits an extension of a fibre cokernel by a boundary
kernel.  An arbitrary projective splitting is unsuitable for the final inclusion calculation.
This file instead uses an explicit swept-cycle section and proves the resulting two coordinates.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData} {D : A.SectionSevenEllipticTwoDiscCoverData}
  (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)

namespace SectionSevenEllipticTwoDiscHomologyCoordinates

include B

/-- The degree-one fibre-cokernel coordinate. -/
public noncomputable def degreeOneCoinvariantEquiv :
    (presentationOne (D := D)).Coinvariants ≃ₗ[ℤ] ℤ :=
  (cokernelEquivOfComm B.bandOne.toIntLinearEquiv B.sidesOne.toIntLinearEquiv
    (presentationOne (D := D)).highDifference.toIntLinearMap ellipticActualHOneLinear
      B.differenceOne_linear_comm).trans ellipticActualHOneCokernelEquivInt

/-- Degree zero has no invariant term because the two sides and their overlap are connected. -/
public def degreeOneInvariantEquiv :
    (presentationOne (D := D)).Invariants ≃ₗ[ℤ] (Fin 0 → ℤ) :=
  kernelEquivFinZeroOfInjective
    (presentationOne (D := D)).lowDifference.toIntLinearMap B.differenceZero_injective

/-- The unique normalized splitting when the invariant term is zero. -/
public def degreeOneZeroSplitting :
    WangHomologyPresentation.NormalizedSplitting (presentationOne (D := D)) where
  sweptSection := 0
  rightInverse := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply,
      LinearMap.id_apply]
    apply B.differenceZero_injective
    change (presentationOne (D := D)).lowDifference
        ((presentationOne (D := D)).boundary 0) =
      (presentationOne (D := D)).lowDifference x.1
    rw [(presentationOne (D := D)).lowDifference_boundary]
    exact (LinearMap.mem_ker.mp x.2).symm

/-- Canonical degree-one coordinates on the literal union of the two elliptic sides. -/
public noncomputable def normalizedUnionHomologyOneEquiv :
    IntegralSingularHomology 1
        (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior) ≃+
      (Fin 1 → ℤ) :=
  ((WangHomologyPresentation.NormalizedSplitting.totalLinearEquivOfEndCoordinates
      (presentationOne (D := D)) (degreeOneZeroSplitting B) (degreeOneCoinvariantEquiv B)
      (degreeOneInvariantEquiv B)).trans intProdFinZeroEquivFinOne).toAddEquiv

/-- Canonical degree-one coordinates on the actual elliptic interior. -/
public noncomputable def normalizedEllipticInteriorHomologyOneEquiv :
    IntegralSingularHomology 1 A.SectionSevenEllipticInterior ≃+ (Fin 1 → ℤ) := by
  let eTop := integralSingularHomologyEquiv 1
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  exact eTop.symm.trans (normalizedUnionHomologyOneEquiv B)

/-- Fibre coinvariants have their prescribed scalar coordinate in degree one. -/
public theorem normalizedUnionHomologyOneEquiv_coinvariantsToTotal
    (c : (presentationOne (D := D)).Coinvariants) :
    normalizedUnionHomologyOneEquiv B
        ((presentationOne (D := D)).coinvariantsToTotal c) =
      ![degreeOneCoinvariantEquiv B c] := by
  change intProdFinZeroEquivFinOne
      ((WangHomologyPresentation.NormalizedSplitting.totalLinearEquivOfEndCoordinates
        (presentationOne (D := D)) (degreeOneZeroSplitting B) (degreeOneCoinvariantEquiv B)
        (degreeOneInvariantEquiv B))
          ((presentationOne (D := D)).coinvariantsToTotal c)) = _
  rw [show (WangHomologyPresentation.NormalizedSplitting.totalLinearEquivOfEndCoordinates
        (presentationOne (D := D)) (degreeOneZeroSplitting B) (degreeOneCoinvariantEquiv B)
        (degreeOneInvariantEquiv B))
          ((presentationOne (D := D)).coinvariantsToTotal c) =
      (degreeOneCoinvariantEquiv B c, 0) by
        change ((degreeOneCoinvariantEquiv B).prodCongr (degreeOneInvariantEquiv B))
          (WangHomologyPresentation.NormalizedSplitting.totalLinearEquiv
            (presentationOne (D := D)) (degreeOneZeroSplitting B)
              ((presentationOne (D := D)).coinvariantsToTotal c)) = _
        rw [WangHomologyPresentation.NormalizedSplitting.totalLinearEquiv_coinvariantsToTotal]
        apply Prod.ext
        · rfl
        · exact Subsingleton.elim _ _]
  funext i
  fin_cases i
  rfl

/-- The degree-two fibre-cokernel coordinate from the corrected two-disc difference map. -/
public noncomputable def degreeTwoCoinvariantEquiv :
    (presentationTwo (D := D)).Coinvariants ≃ₗ[ℤ] ℤ :=
  (cokernelEquivOfComm B.bandTwo.toIntLinearEquiv B.sidesTwo.toIntLinearEquiv
    (presentationTwo (D := D)).highDifference.toIntLinearMap alphaTwoLinear
      B.differenceTwo_linear_comm).trans alphaTwoCokernelEquivInt

/-- The swept-cycle boundary coordinate, identified with the kernel generator of the actual
degree-one difference matrix. -/
public noncomputable def degreeTwoInvariantEquiv :
    (presentationTwo (D := D)).Invariants ≃ₗ[ℤ] ℤ :=
  (kernelEquivOfComm B.bandOne.toIntLinearEquiv B.sidesOne.toIntLinearEquiv
    (presentationTwo (D := D)).lowDifference.toIntLinearMap ellipticActualHOneLinear
      B.differenceOne_linear_comm).trans ellipticActualHOneKernelEquivInt

/-- A chosen degree-two class whose Mayer--Vietoris boundary is the positive invariant generator
determines a splitting.  The boundary equality is deliberately explicit: no arbitrary splitting
is asserted to have the paper's geometric normalization. -/
public noncomputable def degreeTwoSplittingOfGenerator
    (g : IntegralSingularHomology 2
      (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior))
    (hboundary :
      (presentationTwo (D := D)).totalToInvariants g =
        (degreeTwoInvariantEquiv B).symm 1) :
    WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)) := by
  let P := presentationTwo (D := D)
  let e := degreeTwoInvariantEquiv B
  let s : P.Invariants →ₗ[ℤ] IntegralSingularHomology 2
      (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior) :=
    ((LinearMap.lsmul ℤ _).flip g).comp e.toLinearMap
  refine
    { sweptSection := s
      rightInverse := ?_ }
  apply LinearMap.ext
  intro z
  change P.totalToInvariants ((e z) • g) = z
  rw [map_smul, hboundary]
  rw [← e.symm.map_smul]
  simpa using e.symm_apply_apply z

/-- Pull the actual cusp-collar inclusion into the literal union used by the elliptic
Mayer--Vietoris presentation. -/
public noncomputable def cuspToEllipticUnionHomology
    (D : A.SectionSevenEllipticTwoDiscCoverData) (k : ℕ)
    (x : IntegralSingularHomology k (A.openEmbeddingStarData.collarSource 0)) :
    IntegralSingularHomology k
        (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior) :=
  (integralSingularHomologyEquiv k
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)).symm
    (integralSingularHomologyMap k
      (IntegralMayerVietoris.interToLeft
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4))
        ((A.openEmbeddingStarData.SectionSevenMayerVietorisCover).piece 3))
      (integralSingularHomologyEquiv k
        A.cuspCollarToSectionSevenFinalOverlapHomeomorph x))

/-- The actual cusp collar's second suspension basis class, included into the literal elliptic
two-disc union. -/
public noncomputable def degreeTwoCuspE5Generator :
    IntegralSingularHomology 2
      (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior) :=
  cuspToEllipticUnionHomology D 2
    (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))

/-- A boundary-coordinate formula for every cusp class orients the included `e₅` generator. -/
public theorem degreeTwoCuspE5Boundary_of_coordinates
    (hboundaryCoordinates : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      degreeTwoInvariantEquiv B
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2 x)) =
        A.actualCuspRawHomologyTwoEquiv x 5) :
    (presentationTwo (D := D)).totalToInvariants
        (degreeTwoCuspE5Generator (A := A) (D := D)) =
      (degreeTwoInvariantEquiv B).symm 1 := by
  apply (degreeTwoInvariantEquiv B).injective
  rw [LinearEquiv.apply_symm_apply]
  simpa [degreeTwoCuspE5Generator] using
    hboundaryCoordinates
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))

/-- The cusp `e₅` class supplies the degree-two splitting once its geometric boundary is
identified with the positive invariant generator. -/
public noncomputable def degreeTwoSplittingOfCuspE5
    (hboundary :
      (presentationTwo (D := D)).totalToInvariants (degreeTwoCuspE5Generator (A := A) (D := D)) =
        (degreeTwoInvariantEquiv B).symm 1) :
    WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)) :=
  degreeTwoSplittingOfGenerator B (degreeTwoCuspE5Generator (A := A) (D := D)) hboundary

/-- The full boundary-coordinate comparison canonically selects the splitting generated by the
included positive cusp `e₅` class. -/
public noncomputable def degreeTwoCuspE5SplittingOfCoordinates
    (hboundaryCoordinates : ∀ x : IntegralSingularHomology 2
        (A.openEmbeddingStarData.collarSource 0),
      degreeTwoInvariantEquiv B
          ((presentationTwo (D := D)).totalToInvariants
            (cuspToEllipticUnionHomology D 2 x)) =
        A.actualCuspRawHomologyTwoEquiv x 5) :
    WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)) :=
  degreeTwoSplittingOfCuspE5 B
    (degreeTwoCuspE5Boundary_of_coordinates B hboundaryCoordinates)

/-- The degree-two coordinates on the literal union of the two sides, normalized by an explicit
swept-cycle section. -/
public noncomputable def normalizedUnionHomologyTwoEquiv
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))) :
    IntegralSingularHomology 2
        (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior) ≃+
      (Fin 2 → ℤ) :=
  ((WangHomologyPresentation.NormalizedSplitting.totalLinearEquivOfEndCoordinates
      (presentationTwo (D := D)) S (degreeTwoCoinvariantEquiv B)
      (degreeTwoInvariantEquiv B)).trans intProdEquivFinTwo).toAddEquiv

/-- The second normalized coordinate is the Mayer--Vietoris boundary coordinate and is
independent of the chosen splitting. -/
public theorem normalizedUnionHomologyTwoEquiv_one
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (x : IntegralSingularHomology 2
      (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    normalizedUnionHomologyTwoEquiv B S x 1 =
      degreeTwoInvariantEquiv B ((presentationTwo (D := D)).totalToInvariants x) := by
  rfl

/-- The resulting normalized basis on the actual elliptic interior. -/
public noncomputable def normalizedEllipticInteriorHomologyTwoEquiv
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D))) :
    IntegralSingularHomology 2 A.SectionSevenEllipticInterior ≃+ (Fin 2 → ℤ) :=
  let eTop := integralSingularHomologyEquiv 2
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  eTop.symm.trans (normalizedUnionHomologyTwoEquiv B S)

/-- In normalized coordinates, a fibre coinvariant followed by a swept cycle has exactly the
two prescribed end coordinates. -/
public theorem normalizedUnionHomologyTwoEquiv_add
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (c : (presentationTwo (D := D)).Coinvariants) (z : (presentationTwo (D := D)).Invariants) :
    normalizedUnionHomologyTwoEquiv B S
        ((presentationTwo (D := D)).coinvariantsToTotal c + S.sweptSection z) =
      ![degreeTwoCoinvariantEquiv B c, degreeTwoInvariantEquiv B z] := by
  rw [map_add]
  change intProdEquivFinTwo
      ((WangHomologyPresentation.NormalizedSplitting.totalLinearEquivOfEndCoordinates
        (presentationTwo (D := D)) S (degreeTwoCoinvariantEquiv B)
        (degreeTwoInvariantEquiv B)) ((presentationTwo (D := D)).coinvariantsToTotal c)) +
    intProdEquivFinTwo
      ((WangHomologyPresentation.NormalizedSplitting.totalLinearEquivOfEndCoordinates
        (presentationTwo (D := D)) S (degreeTwoCoinvariantEquiv B)
        (degreeTwoInvariantEquiv B)) (S.sweptSection z)) = _
  have hc := WangHomologyPresentation.NormalizedSplitting.totalLinearEquiv_coinvariantsToTotal
    (presentationTwo (D := D)) S c
  have hz := WangHomologyPresentation.NormalizedSplitting.totalLinearEquiv_sweptSection
    (presentationTwo (D := D)) S z
  rw [show (WangHomologyPresentation.NormalizedSplitting.totalLinearEquivOfEndCoordinates
        (presentationTwo (D := D)) S (degreeTwoCoinvariantEquiv B)
        (degreeTwoInvariantEquiv B)) ((presentationTwo (D := D)).coinvariantsToTotal c) =
      (degreeTwoCoinvariantEquiv B c, 0) by
        change ((degreeTwoCoinvariantEquiv B).prodCongr (degreeTwoInvariantEquiv B))
          (WangHomologyPresentation.NormalizedSplitting.totalLinearEquiv
            (presentationTwo (D := D)) S
              ((presentationTwo (D := D)).coinvariantsToTotal c)) = _
        rw [hc]
        apply Prod.ext
        · rfl
        · change degreeTwoInvariantEquiv B 0 = 0
          exact map_zero _,
    show (WangHomologyPresentation.NormalizedSplitting.totalLinearEquivOfEndCoordinates
        (presentationTwo (D := D)) S (degreeTwoCoinvariantEquiv B)
        (degreeTwoInvariantEquiv B)) (S.sweptSection z) =
      (0, degreeTwoInvariantEquiv B z) by
        change ((degreeTwoCoinvariantEquiv B).prodCongr (degreeTwoInvariantEquiv B))
          (WangHomologyPresentation.NormalizedSplitting.totalLinearEquiv
            (presentationTwo (D := D)) S (S.sweptSection z)) = _
        rw [hz]
        apply Prod.ext
        · change degreeTwoCoinvariantEquiv B 0 = 0
          exact map_zero _
        · rfl]
  funext i
  fin_cases i <;> simp [intProdEquivFinTwo]

end SectionSevenEllipticTwoDiscHomologyCoordinates

end SphereSixComplex.Geometry.PaperAnalyticData
