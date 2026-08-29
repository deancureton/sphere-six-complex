module

public import SphereSixComplex.Topology.PaperAffineCyclicQuotientHomologyCoordinates

/-!
# Degree-two deck invariance for affine cyclic torus covers

The covering projection is invariant under the affine cyclic generator.  This file transports
that point-set identity through the standard exterior-square basis on the covering four-torus.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory

namespace SphereSixComplex.Topology.AffineCyclicCoverDegreeTwoInvariance

open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticFamilySpecialization
open LatticeData Periods
open PaperEllipticFillingRadialRetraction
open PaperEllipticReducedCentralFiberCoverModels
open PaperMultipleFiberHOneTopology
open PaperAffineCyclicQuotientHomologyCoordinates

private theorem homologyMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (k : ℕ) (f : C(X, Y)) (g : C(Y, Z))
    (x : IntegralSingularHomology k X) :
    integralSingularHomologyMap k (g.comp f) x =
      integralSingularHomologyMap k g (integralSingularHomologyMap k f x) := by
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (g.comp f))) x = _
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g from rfl,
    Functor.map_comp]
  rfl

private theorem homologyEquiv_map_symm {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) (e : X ≃ₜ Y) (x : IntegralSingularHomology k Y) :
    integralSingularHomologyEquiv k e
        (integralSingularHomologyMap k ⟨e.symm, e.symm.continuous⟩ x) = x :=
  (integralSingularHomologyEquiv k e).apply_symm_apply x

variable {m : ℕ} [NeZero m] {p : SphereSixComplex.Periods.Parameters}
  {D : RadialEllipticActionData m (AdditiveTorus p)}

/-- The transported degree-two basis intertwines the deck generator with the exterior-square
action of its integral linear part. -/
public theorem centralFiberCoverSourceDegreeTwoBasis_generator
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (z : IntegralSingularHomology 2 (RadialEllipticActionData.centralFiberCoverSource D)) :
    (affineCyclicCentralFiberCoverSourceHomologyBasis P).degreeTwo
        (integralSingularHomologyMap 2
          (EstablishedAffineCyclicQuotientHomology.centralFiberCoverGenerator P) z) =
      exteriorSquareMap P.affine.latticeMap
        ((affineCyclicCentralFiberCoverSourceHomologyBasis P).degreeTwo z) := by
  have hnat := (EstablishedTorusHomology.additiveTorusHomologyBasis_naturality p P.fullRank
    P.affine).2
  change (EstablishedTorusHomology.additiveTorusHomologyBasis p P.fullRank).degreeTwo
      (integralSingularHomologyEquiv 2
        (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D)
        (integralSingularHomologyMap 2
          (EstablishedAffineCyclicQuotientHomology.centralFiberCoverGenerator P) z)) = _
  rw [EstablishedAffineCyclicQuotientHomology.centralFiberCoverGenerator,
    homologyMap_comp, homologyMap_comp, homologyEquiv_map_symm, hnat]
  rfl

/-- The degree-two covering map is invariant under the exterior-square action of the deck
generator. -/
public theorem coverProjection_degreeTwo_invariant
    (P : AffineCyclicCentralFiberPresentationData m p D) (x : Fin 6 → ℤ) :
    integralSingularHomologyMap 2
        (RadialEllipticActionData.centralFiberCoverProjection D)
        ((affineCyclicCentralFiberCoverSourceHomologyBasis P).degreeTwo.symm
          (exteriorSquareMap P.affine.latticeMap x)) =
      integralSingularHomologyMap 2
        (RadialEllipticActionData.centralFiberCoverProjection D)
        ((affineCyclicCentralFiberCoverSourceHomologyBasis P).degreeTwo.symm x) := by
  have hbasis := centralFiberCoverSourceDegreeTwoBasis_generator P
    ((affineCyclicCentralFiberCoverSourceHomologyBasis P).degreeTwo.symm x)
  rw [(affineCyclicCentralFiberCoverSourceHomologyBasis P).degreeTwo.apply_symm_apply] at hbasis
  have hsymm :
      (affineCyclicCentralFiberCoverSourceHomologyBasis P).degreeTwo.symm
          (exteriorSquareMap P.affine.latticeMap x) =
        integralSingularHomologyMap 2
          (EstablishedAffineCyclicQuotientHomology.centralFiberCoverGenerator P)
          ((affineCyclicCentralFiberCoverSourceHomologyBasis P).degreeTwo.symm x) := by
    rw [← hbasis,
      (affineCyclicCentralFiberCoverSourceHomologyBasis P).degreeTwo.symm_apply_apply]
  rw [hsymm, ← homologyMap_comp,
    EstablishedAffineCyclicQuotientHomology.centralFiberCoverProjection_comp_generator
      EstablishedAffineCyclicQuotientHomology.isCentralFiberCoverSourceCoordinate P]

end SphereSixComplex.Topology.AffineCyclicCoverDegreeTwoInvariance

end
