module

public import SphereSixComplex.Topology.HurewiczWhitehead
public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasis
public import SphereSixComplex.Topology.SectionSevenMayerVietorisHomologyAssembly
public import SphereSixComplex.Geometry.PaperOpenEmbeddingStar

/-!
# The two-disc cover of the elliptic interior

The Mayer--Vietoris maps `alphaOneMatrix` and `alphaTwoMatrix` in Section 7 come from a
separate cover of the cusp-complement by two elliptic sides.  Their intersection lies over a
contractible band and is homotopy equivalent to one regular four-torus.  It is not one of the
successive collar overlaps in the four-piece star cover.

This file records only the geometric comparison data for that source-faithful cover.  It does
not assert that the data exist and makes no homology-rank or matrix claim.  Homotopy invariance
and functoriality formally identify its Mayer--Vietoris difference map with the two actual
finite-cover projections in every degree.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticFamilySpecialization
open Topology.PaperEllipticFillingRadialRetraction
open Topology.PaperEllipticReducedCentralFiberCoverModels

namespace Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The actual cusp-complement: the central family with both elliptic fillings attached. -/
public abbrev SectionSevenEllipticInterior :=
  (A.openEmbeddingStarData.SectionSevenMayerVietorisCover).stage (2 : Fin 4)

/-- Geometric data for the two-disc cover used in Lemma 7.19.  The compatibility fields say
that, after trivializing the band fibre and retracting either side to its reduced central fibre,
the two inclusions are the actual order-three and order-four finite-cover projections. -/
public structure SectionSevenEllipticTwoDiscCoverData where
  orderThreeSide : Set A.SectionSevenEllipticInterior
  orderFourSide : Set A.SectionSevenEllipticInterior
  orderThreeSide_isOpen : IsOpen orderThreeSide
  orderFourSide_isOpen : IsOpen orderFourSide
  sides_cover : orderThreeSide ∪ orderFourSide = Set.univ
  bandParameter : SphereSixComplex.Periods.Parameters
  bandFullRank : FullRank bandParameter
  bandHomotopyEquiv :
    (orderThreeSide ∩ orderFourSide : Set A.SectionSevenEllipticInterior) ≃ₕ
      AdditiveTorus bandParameter
  orderThreeSideHomotopyEquiv :
    orderThreeSide ≃ₕ OrderThreeReducedCentralFiber A.periods
  orderFourSideHomotopyEquiv :
    orderFourSide ≃ₕ OrderFourReducedCentralFiber A.periods
  bandToOrderThreeCoverSource :
    AdditiveTorus bandParameter ≃ₜ
      RadialEllipticActionData.centralFiberCoverSource
        (orderThreeRadialActionData A.periods)
  bandToOrderFourCoverSource :
    AdditiveTorus bandParameter ≃ₜ
      RadialEllipticActionData.centralFiberCoverSource
        (orderFourRadialActionData A.periods)
  orderThree_inclusion_compatibility :
    (orderThreeSideHomotopyEquiv.toFun.comp
      (IntegralMayerVietoris.interToLeft orderThreeSide orderFourSide)).Homotopic
        ((RadialEllipticActionData.centralFiberCoverProjection
            (orderThreeRadialActionData A.periods)).comp
          ⟨bandToOrderThreeCoverSource,
            bandToOrderThreeCoverSource.continuous⟩ |>.comp bandHomotopyEquiv.toFun)
  orderFour_inclusion_compatibility :
    (orderFourSideHomotopyEquiv.toFun.comp
      (IntegralMayerVietoris.interToRight orderThreeSide orderFourSide)).Homotopic
        ((RadialEllipticActionData.centralFiberCoverProjection
            (orderFourRadialActionData A.periods)).comp
          ⟨bandToOrderFourCoverSource,
            bandToOrderFourCoverSource.continuous⟩ |>.comp bandHomotopyEquiv.toFun)

namespace SectionSevenEllipticTwoDiscCoverData

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

/-- The homology basis change from the actual band overlap to its selected regular fibre. -/
public noncomputable def bandHomologyEquiv (k : ℕ) :
    IntegralSingularHomology k
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior) ≃+
      IntegralSingularHomology k (AdditiveTorus D.bandParameter) :=
  integralSingularHomologyEquivOfHomotopyEquiv k D.bandHomotopyEquiv

/-- The product basis change from the two actual sides to the two reduced elliptic fibres. -/
public noncomputable def sideHomologyEquiv (k : ℕ) :
    (IntegralSingularHomology k D.orderThreeSide ×
      IntegralSingularHomology k D.orderFourSide) ≃+
    (IntegralSingularHomology k (OrderThreeReducedCentralFiber A.periods) ×
      IntegralSingularHomology k (OrderFourReducedCentralFiber A.periods)) :=
  (integralSingularHomologyEquivOfHomotopyEquiv k
      D.orderThreeSideHomotopyEquiv).prodCongr
    (integralSingularHomologyEquivOfHomotopyEquiv k
      D.orderFourSideHomotopyEquiv)

/-- The order-three band fibre followed by the actual central-fibre covering projection. -/
public noncomputable def orderThreeBandProjection :
    C(AdditiveTorus D.bandParameter, OrderThreeReducedCentralFiber A.periods) :=
  (RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
    ⟨D.bandToOrderThreeCoverSource, D.bandToOrderThreeCoverSource.continuous⟩

/-- The order-four band fibre followed by the actual central-fibre covering projection. -/
public noncomputable def orderFourBandProjection :
    C(AdditiveTorus D.bandParameter, OrderFourReducedCentralFiber A.periods) :=
  (RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
    ⟨D.bandToOrderFourCoverSource, D.bandToOrderFourCoverSource.continuous⟩

private theorem integralSingularHomologyMap_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (k : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularHomologyMap k (g.comp f) =
      (integralSingularHomologyMap k g).comp (integralSingularHomologyMap k f) := by
  ext x
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (g.comp f))) x = _
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g by rfl,
    Functor.map_comp]
  rfl

private theorem integralSingularHomologyMap_homotopic
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) {f g : C(X, Y)} (h : f.Homotopic g) :
    integralSingularHomologyMap k f = integralSingularHomologyMap k g := by
  ext x
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom f)) x =
    ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom g)) x
  rw [SphereSixComplex.integralSingularHomologyMap_eq_of_homotopic h k]

private theorem homotopyEquiv_homology_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) (e : X ≃ₕ Y) (x : IntegralSingularHomology k X) :
    integralSingularHomologyEquivOfHomotopyEquiv k e x =
      integralSingularHomologyMap k e.toFun x :=
  rfl

/-- In the homotopy-equivalence coordinates of the two-disc model, the actual
Mayer--Vietoris difference map is the pair of finite-cover projection maps, with the standard
minus sign on the order-four side. -/
public theorem differenceMap_conjugacy (k : ℕ)
    (x : IntegralSingularHomology k
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    D.sideHomologyEquiv k
        (IntegralMayerVietoris.differenceMap
          D.orderThreeSide D.orderFourSide k x) =
      (integralSingularHomologyMap k D.orderThreeBandProjection
          (D.bandHomologyEquiv k x),
        -integralSingularHomologyMap k D.orderFourBandProjection
          (D.bandHomologyEquiv k x)) := by
  apply Prod.ext
  · change ((integralSingularHomologyMap k D.orderThreeSideHomotopyEquiv.toFun).comp
        (integralSingularHomologyMap k
          (IntegralMayerVietoris.interToLeft D.orderThreeSide D.orderFourSide))) x =
      integralSingularHomologyMap k D.orderThreeBandProjection
        (integralSingularHomologyMap k D.bandHomotopyEquiv.toFun x)
    rw [← integralSingularHomologyMap_comp]
    rw [integralSingularHomologyMap_homotopic k
      D.orderThree_inclusion_compatibility]
    rw [integralSingularHomologyMap_comp]
    rfl
  · change integralSingularHomologyMap k D.orderFourSideHomotopyEquiv.toFun
        (-(integralSingularHomologyMap k
          (IntegralMayerVietoris.interToRight D.orderThreeSide D.orderFourSide) x)) =
      -integralSingularHomologyMap k D.orderFourBandProjection
        (integralSingularHomologyMap k D.bandHomotopyEquiv.toFun x)
    rw [map_neg]
    change -((integralSingularHomologyMap k D.orderFourSideHomotopyEquiv.toFun).comp
        (integralSingularHomologyMap k
          (IntegralMayerVietoris.interToRight D.orderThreeSide D.orderFourSide))) x =
      -integralSingularHomologyMap k D.orderFourBandProjection
        (integralSingularHomologyMap k D.bandHomotopyEquiv.toFun x)
    congr 1
    rw [← integralSingularHomologyMap_comp]
    rw [integralSingularHomologyMap_homotopic k
      D.orderFour_inclusion_compatibility]
    rw [integralSingularHomologyMap_comp]
    rfl

/-- Degree-one specialization of `differenceMap_conjugacy`. -/
public theorem differenceMap_one_conjugacy
    (x : IntegralSingularHomology 1
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    D.sideHomologyEquiv 1
        (IntegralMayerVietoris.differenceMap
          D.orderThreeSide D.orderFourSide 1 x) =
      (integralSingularHomologyMap 1 D.orderThreeBandProjection
          (D.bandHomologyEquiv 1 x),
        -integralSingularHomologyMap 1 D.orderFourBandProjection
          (D.bandHomologyEquiv 1 x)) :=
  D.differenceMap_conjugacy 1 x

/-- Degree-two specialization of `differenceMap_conjugacy`. -/
public theorem differenceMap_two_conjugacy
    (x : IntegralSingularHomology 2
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :
    D.sideHomologyEquiv 2
        (IntegralMayerVietoris.differenceMap
          D.orderThreeSide D.orderFourSide 2 x) =
      (integralSingularHomologyMap 2 D.orderThreeBandProjection
          (D.bandHomologyEquiv 2 x),
        -integralSingularHomologyMap 2 D.orderFourBandProjection
          (D.bandHomologyEquiv 2 x)) :=
  D.differenceMap_conjugacy 2 x

end SectionSevenEllipticTwoDiscCoverData

end Geometry.PaperAnalyticData

end SphereSixComplex
