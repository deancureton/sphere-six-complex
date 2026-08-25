module

public import SphereSixComplex.Topology.NormalizedWangHomologySplitting
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
