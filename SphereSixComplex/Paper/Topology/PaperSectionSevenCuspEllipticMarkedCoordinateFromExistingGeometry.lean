module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction
public import SphereSixComplex.Paper.Geometry.CuspCollarPairProperness
public import SphereSixComplex.Paper.Geometry.RealPeriodTrivialization
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryUniversalCover
public import SphereSixComplex.Prerequisites.Topology.MayerVietoris
public import Mathlib.Algebra.Category.Grp.EpiMono

public import SphereSixComplex.Paper.Topology.PaperCuspGeometricSpecializationProof

/-!
# Coordinates of the included elliptic band

The canonical band inclusion maps fiber homology into the Wang coinvariant summand. The
normalized union coordinates identify this actual map with the marked coinvariant coordinates.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.LatticeData
open SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.CuspMonodromyCoinvariants
open EllipticInteriorMarkedCycleData
open EllipticTwoDiscHomologyCoordinates
open EllipticTwoDiscCoverData

variable {A : AnalyticData} (D : A.EllipticTwoDiscCoverData)

namespace EllipticTwoDiscCoverData


private theorem degreeTwoCoinvariantEquiv_mk
    (B : A.EllipticTwoDiscHomologyCoordinates D)
    (z : IntegralSingularHomology 2 D.orderThreeSide ×
      IntegralSingularHomology 2 D.orderFourSide) :
    B.degreeTwoCoinvariantEquiv (Submodule.Quotient.mk z) =
      alphaTwoFunctional (B.sidesTwo z) := by
  rfl

/-- Include the elliptic band into the literal union through the order-three side. -/
public def canonicalBandToEllipticUnionMap :
    C((D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior),
      (D.orderThreeSide ∪ D.orderFourSide : Set A.ellipticInterior)) :=
  (IntegralMayerVietoris.leftToUnion D.orderThreeSide D.orderFourSide).comp
    (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide)

public def canonicalBandToEllipticInteriorInclusionMap :
    C((D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior),
      A.ellipticInterior) :=
  ⟨Subtype.val, continuous_subtype_val⟩

public theorem ellipticInteriorEquiv_symm_bandInclusion
    (k : ℕ)
    (x : IntegralSingularHomology k
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :
    (integralSingularHomologyEquiv k
      (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.ellipticInterior)
        (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)).symm
        (integralSingularHomologyMap k
          (canonicalBandToEllipticInteriorInclusionMap D) x) =
      integralSingularHomologyMap k (canonicalBandToEllipticUnionMap D) x := by
  let eTop := integralSingularHomologyEquiv k
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.ellipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  apply eTop.injective
  rw [eTop.apply_symm_apply]
  change integralSingularHomologyMap k
      (canonicalBandToEllipticInteriorInclusionMap D) x =
    integralSingularHomologyMap k
      ⟨topologicalSubsetHomeomorphOfEqUniv
        (TopCat.of A.ellipticInterior)
        (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover,
        (topologicalSubsetHomeomorphOfEqUniv
          (TopCat.of A.ellipticInterior)
          (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover).continuous⟩
      (integralSingularHomologyMap k (canonicalBandToEllipticUnionMap D) x)
  rw [integralSingularHomologyMap_comp_wang]
  congr 2


public theorem canonicalBandToEllipticUnionHomologyTwo_eq_coinvariants
    (x : IntegralSingularHomology 2
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :
    integralSingularHomologyMap 2 (canonicalBandToEllipticUnionMap D) x =
      (presentationTwo (D := D)).coinvariantsToTotal
        (Submodule.Quotient.mk
          (integralSingularHomologyMap 2
            (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0)) := by
  unfold canonicalBandToEllipticUnionMap
  rw [← integralSingularHomologyMap_comp_wang]
  rw [WangHomologyPresentation.coinvariantsToTotal, Submodule.liftQ_apply]
  change _ = IntegralMayerVietoris.sumMap D.orderThreeSide D.orderFourSide 2 (_, 0)
  simp [IntegralMayerVietoris.sumMap]


public theorem normalizedUnionHomologyTwoEquiv_canonicalBand
    (B : A.EllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (x : IntegralSingularHomology 2
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :
    B.normalizedUnionHomologyTwoEquiv S
        (integralSingularHomologyMap 2 (canonicalBandToEllipticUnionMap D) x) 0 =
      alphaTwoFunctional
        (B.sidesTwo
          (integralSingularHomologyMap 2
            (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0)) := by
  rw [canonicalBandToEllipticUnionHomologyTwo_eq_coinvariants]
  let c : (presentationTwo (D := D)).Coinvariants :=
    Submodule.Quotient.mk
      (integralSingularHomologyMap 2
        (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0)
  have h := congrFun (B.normalizedUnionHomologyTwoEquiv_add S c 0) (0 : Fin 2)
  simp only [map_zero, add_zero] at h
  rw [h]
  exact degreeTwoCoinvariantEquiv_mk D B _


end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.AnalyticData

end
