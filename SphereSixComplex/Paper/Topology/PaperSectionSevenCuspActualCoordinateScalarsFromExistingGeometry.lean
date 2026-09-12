module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction
public import SphereSixComplex.Paper.Geometry.CuspCollarPairProperness
public import SphereSixComplex.Paper.Geometry.RealPeriodTrivialization
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryUniversalCover
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspEllipticMarkedCoordinateFromExistingGeometry

/-!
# Actual cusp coordinate scalars from the existing geometry

The order-three side of the elliptic two-disc cover gives the literal scalar fibre coordinates.
For the actual affine cover, its period marking then evaluates the selected cusp fibre bases.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Matrix Set
open scoped ContinuousMap

namespace SphereSixComplex

open SphereSixComplex.Geometry SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open EllipticFilling
open Topology.FiniteCoverPerfectPairing
open EllipticFilling


namespace Geometry.AnalyticData

open SphereSixComplex.LatticeData
open SphereSixComplex.MultipleFiberCoinvariants
open EllipticTwoDiscHomologyCoordinates

variable {A : AnalyticData} {D : A.EllipticTwoDiscCoverData}


namespace EllipticTwoDiscCoverData

private theorem sideHomologyEquiv_interToLeft_aux (k : ℕ)
    (x : IntegralSingularHomology k
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :
    D.sideHomologyEquiv k
        (integralSingularHomologyMap k
          (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0) =
      (integralSingularHomologyMap k D.orderThreeBandProjection
          (D.bandHomologyEquiv k x), 0) := by
  have hMap : integralSingularHomologyMap k
      (D.orderThreeSideHomotopyEquiv.toFun.comp
        (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide)) =
      integralSingularHomologyMap k
        (D.orderThreeBandProjection.comp D.bandHomotopyEquiv.toFun) := by
    ext y
    change ConcreteCategory.hom
        (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
          (TopCat.ofHom (D.orderThreeSideHomotopyEquiv.toFun.comp
            (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide)))) y =
      ConcreteCategory.hom
        (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
          (TopCat.ofHom (D.orderThreeBandProjection.comp D.bandHomotopyEquiv.toFun))) y
    rw [SphereSixComplex.integralSingularHomologyMap_eq_of_homotopic
      D.orderThree_inclusion_compatibility k]
    rfl
  apply Prod.ext
  · change integralSingularHomologyMap k D.orderThreeSideHomotopyEquiv.toFun
        (integralSingularHomologyMap k
          (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x) =
      integralSingularHomologyMap k D.orderThreeBandProjection
        (integralSingularHomologyMap k D.bandHomotopyEquiv.toFun x)
    calc
      _ = integralSingularHomologyMap k
          (D.orderThreeSideHomotopyEquiv.toFun.comp
            (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide)) x :=
        SphereSixComplex.integralSingularHomologyMap_comp_wang _ _ _ _
      _ = integralSingularHomologyMap k
          (D.orderThreeBandProjection.comp D.bandHomotopyEquiv.toFun) x :=
        DFunLike.congr_fun hMap x
      _ = _ := (SphereSixComplex.integralSingularHomologyMap_comp_wang _ _ _ _).symm
  · change integralSingularHomologyMap k D.orderFourSideHomotopyEquiv.toFun 0 = 0
    exact map_zero _


/-- The order-three inclusion has its literal four side coordinates in degree two. -/
public theorem actualHomologyCoordinates_sidesTwo_interToLeft
    (N : A.EllipticBandHomologyAlignment D)
    (x : IntegralSingularHomology 2
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :
    N.actualHomologyCoordinates.sidesTwo
        (integralSingularHomologyMap 2
          (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0) =
      ![(alphaTwoMatrix *ᵥ N.actualHomologyCoordinates.bandTwo x) 0,
        (alphaTwoMatrix *ᵥ N.actualHomologyCoordinates.bandTwo x) 1, 0, 0] := by
  let R := ellipticFiniteCoverHomologyRealization A.periods
    (nonempty_actualEllipticDegreeTwoHomologyBasisFiniteData A)
  change EllipticBandHomologyAlignment.sidesTwo (D := D) R
      (integralSingularHomologyMap 2
        (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide) x, 0) =
    ![(alphaTwoMatrix *ᵥ EllipticBandHomologyAlignment.bandTwo (D := D) x) 0,
      (alphaTwoMatrix *ᵥ EllipticBandHomologyAlignment.bandTwo (D := D) x) 1, 0, 0]
  unfold EllipticBandHomologyAlignment.sidesTwo
  simp only [AddEquiv.trans_apply]
  rw [sideHomologyEquiv_interToLeft_aux]
  change ![
      R.orderThreeTwoBasis A.periods
        (integralSingularHomologyMap 2 D.orderThreeBandProjection
          (D.bandHomologyEquiv 2 x)) 0,
      R.orderThreeTwoBasis A.periods
        (integralSingularHomologyMap 2 D.orderThreeBandProjection
          (D.bandHomologyEquiv 2 x)) 1,
      R.orderFourTwoBasis A.periods 0 0, R.orderFourTwoBasis A.periods 0 1] = _
  rw [map_zero, EllipticBandHomologyAlignment.orderThreeTwo_projection_bandTwo]
  rfl


/-- The order-three one-sided inclusion has scalar coordinate `12 q₂ + 2 q₃` in degree two. -/
public theorem actualHomologyCoordinates_normalizedUnionHomologyTwoEquiv_canonicalBand_zero
    (N : A.EllipticBandHomologyAlignment D)
    (S : WangHomologyPresentation.NormalizedSplitting (presentationTwo (D := D)))
    (x : IntegralSingularHomology 2
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :
    N.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv S
        (integralSingularHomologyMap 2 D.canonicalBandToEllipticUnionMap x) 0 =
      12 * N.actualHomologyCoordinates.bandTwo x 2 +
        2 * N.actualHomologyCoordinates.bandTwo x 3 := by
  rw [D.normalizedUnionHomologyTwoEquiv_canonicalBand]
  rw [D.actualHomologyCoordinates_sidesTwo_interToLeft]
  simp [alphaTwoFunctional, alphaTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring


end EllipticTwoDiscCoverData

end Geometry.AnalyticData

end SphereSixComplex

end
