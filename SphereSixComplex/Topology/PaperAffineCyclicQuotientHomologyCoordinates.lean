module

public import SphereSixComplex.Topology.PaperFiniteCyclicQuotientDegreeTwoComparison
public import SphereSixComplex.Topology.PaperMultipleFiberHOneTopology

/-!
# Homology coordinates for affine cyclic torus quotients

This file separates the functorial part of the first-homology quotient presentation from its
existing abstract equivalence.  It proves the canonical lattice-to-presentation coordinates and
isolates the naturality statement needed to identify the actual covering projection.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix

namespace SphereSixComplex.Topology.PaperAffineCyclicQuotientHomologyCoordinates

open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticFamilySpecialization Geometry.GlobalTorusFamily
open LatticeData PaperEllipticFillingRadialRetraction
open PaperEllipticReducedCentralFiberCoverModels PaperLemmaSevenThirteenAlgebra
open PaperMultipleFiberHOneTopology
open PaperFiniteCyclicQuotientDegreeTwoComparison
open TwistObstruction

/-- The canonical map from the covering torus lattice to the abelian multiple-fibre
presentation.  It sends a lattice class to the coinvariant factor and gives it meridian
coordinate zero. -/
public def latticeToMultipleFiberHOnePresentation
    (D : Lattice →ₗ[ℤ] Lattice) (v : Lattice) (m : ℤ) :
    Lattice →ₗ[ℤ] MultipleFiberHOnePresentation D v m :=
  (LinearMap.range (multipleFiberRelationMap D v m)).mkQ.comp
    ((LinearMap.range D).mkQ.prod (0 : Lattice →ₗ[ℤ] ℤ))

/-- Coordinates of the canonical order-three lattice-to-presentation map. -/
public def orderOneLatticeProjectionCoordinates : Lattice →+ IntSquared where
  toFun x := ![3 * gamma x, psiOne x]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    ring

/-- Coordinates of the canonical order-four lattice-to-presentation map. -/
public def orderTwoLatticeProjectionCoordinates : Lattice →+ IntSquared where
  toFun x := ![4 * gamma x, psiTwo x]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    ring

variable {m : ℕ} [NeZero m] {p : SphereSixComplex.Periods.Parameters}
  {D : RadialEllipticActionData m (AdditiveTorus p)}

/-- The standard homology basis on the source of an affine cyclic central-fibre cover. -/
public def affineCyclicCentralFiberCoverSourceHomologyBasis
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    FourTorusHomologyBasis (RadialEllipticActionData.centralFiberCoverSource D) :=
  (EstablishedTorusHomology.additiveTorusHomologyBasis p P.fullRank).homeomorph
    (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D)

/-- Functoriality clause for a degree-one finite-cover presentation.

The existing affine cyclic quotient theorem supplies the quotient basis, but its opaque API does
not expose how that basis acts on the covering projection.  This structure records exactly that
pointwise naturality statement. -/
public structure DegreeOneCoverProjectionRealization
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (projection : C(E, X)) (sourceBasis : IntegralSingularHomology 1 E ≃+ Lattice)
    (quotientBasis : IntegralSingularHomology 1 X ≃+ IntSquared)
    (coordinates : Lattice →+ IntSquared) : Prop where
  projection_coordinates : ∀ x : Lattice,
    quotientBasis
        (integralSingularHomologyMap 1 projection (sourceBasis.symm x)) =
      coordinates x

variable {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)

/-- The exact naturality obligation for the actual order-three finite cover. -/
public abbrev OrderThreeCentralFiberHOneNaturality :=
  DegreeOneCoverProjectionRealization
    (RadialEllipticActionData.centralFiberCoverProjection (orderThreeRadialActionData F))
    (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne
    (orderThreeReducedCentralFiberHOneEquivIntSquared F).toAddEquiv
    orderOneLatticeProjectionCoordinates

/-- The exact naturality obligation for the actual order-four finite cover. -/
public abbrev OrderFourCentralFiberHOneNaturality :=
  DegreeOneCoverProjectionRealization
    (RadialEllipticActionData.centralFiberCoverProjection (orderFourRadialActionData F))
    (orderFourCentralFiberCoverSourceHomologyBasis F).degreeOne
    (orderFourReducedCentralFiberHOneEquivIntSquared F).toAddEquiv
    orderTwoLatticeProjectionCoordinates

/-- The actual order-three projection has coordinates `(3 gamma, psiOne)`. -/
public theorem orderThree_coverProjection_degreeOne_coordinates
    (N : OrderThreeCentralFiberHOneNaturality F) (x : Lattice) :
    orderThreeReducedCentralFiberHOneEquivIntSquared F
        (orderThreeReducedCentralFiberCoverHomologyDegreeOne F x) =
      ![3 * gamma x, psiOne x] := by
  change (orderThreeReducedCentralFiberHOneEquivIntSquared F).toAddEquiv
      (integralSingularHomologyMap 1
        (RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData F))
        ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) = _
  exact N.projection_coordinates x

/-- The actual order-four projection has coordinates `(4 gamma, psiTwo)`. -/
public theorem orderFour_coverProjection_degreeOne_coordinates
    (N : OrderFourCentralFiberHOneNaturality F) (x : Lattice) :
    orderFourReducedCentralFiberHOneEquivIntSquared F
        (orderFourReducedCentralFiberCoverHomologyDegreeOne F x) =
      ![4 * gamma x, psiTwo x] := by
  change (orderFourReducedCentralFiberHOneEquivIntSquared F).toAddEquiv
      (integralSingularHomologyMap 1
        (RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData F))
        ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeOne.symm x)) = _
  exact N.projection_coordinates x

/-- The four finite-cover comparison inputs needed by the elliptic two-disc
Mayer--Vietoris calculation. -/
public structure EllipticFiniteCoverHomologyRealization where
  orderThreeOne : OrderThreeCentralFiberHOneNaturality F
  orderFourOne : OrderFourCentralFiberHOneNaturality F
  orderThreeTwo : OrderThreeReducedCentralFiberDegreeTwoRealization F
  orderFourTwo : OrderFourReducedCentralFiberDegreeTwoRealization F

namespace EllipticFiniteCoverHomologyRealization

/-- The two order-three quotient homology bases. -/
public def orderThreeOneBasis (_R : EllipticFiniteCoverHomologyRealization F) :
    IntegralSingularHomology 1 (OrderThreeReducedCentralFiber F) ≃+ (Fin 2 → ℤ) :=
  (orderThreeReducedCentralFiberHOneEquivIntSquared F).toAddEquiv

public def orderThreeTwoBasis (R : EllipticFiniteCoverHomologyRealization F) :
    IntegralSingularHomology 2 (OrderThreeReducedCentralFiber F) ≃+ (Fin 2 → ℤ) :=
  R.orderThreeTwo.quotientBasis

/-- The two order-four quotient homology bases. -/
public def orderFourOneBasis (_R : EllipticFiniteCoverHomologyRealization F) :
    IntegralSingularHomology 1 (OrderFourReducedCentralFiber F) ≃+ (Fin 2 → ℤ) :=
  (orderFourReducedCentralFiberHOneEquivIntSquared F).toAddEquiv

public def orderFourTwoBasis (R : EllipticFiniteCoverHomologyRealization F) :
    IntegralSingularHomology 2 (OrderFourReducedCentralFiber F) ≃+ (Fin 2 → ℤ) :=
  R.orderFourTwo.quotientBasis

/-- Coordinate formula for the order-three projection in degree one. -/
public theorem orderThreeOne_projection
    (R : EllipticFiniteCoverHomologyRealization F) (x : Lattice) :
    orderThreeOneBasis F R
        (orderThreeReducedCentralFiberCoverHomologyDegreeOne F x) =
      ![3 * gamma x, psiOne x] :=
  orderThree_coverProjection_degreeOne_coordinates F R.orderThreeOne x

/-- Coordinate formula for the order-four projection in degree one. -/
public theorem orderFourOne_projection
    (R : EllipticFiniteCoverHomologyRealization F) (x : Lattice) :
    orderFourOneBasis F R
        (orderFourReducedCentralFiberCoverHomologyDegreeOne F x) =
      ![4 * gamma x, psiTwo x] :=
  orderFour_coverProjection_degreeOne_coordinates F R.orderFourOne x

/-- Coordinate formula for the order-three projection in degree two. -/
public theorem orderThreeTwo_projection
    (R : EllipticFiniteCoverHomologyRealization F)
    (x : PaperPropositionSevenFourteenDegreeTwoAlgebra.DegreeTwoLattice) :
    orderThreeTwoBasis F R
        (orderThreeReducedCentralFiberCoverHomologyDegreeTwo F x) =
      ![(SphereSixComplex.alphaTwoMatrix *ᵥ x) 0,
        (SphereSixComplex.alphaTwoMatrix *ᵥ x) 1] :=
  orderThree_projection_coordinates F R.orderThreeTwo x

/-- Coordinate formula for the order-four projection in degree two. -/
public theorem orderFourTwo_projection
    (R : EllipticFiniteCoverHomologyRealization F)
    (x : PaperPropositionSevenFourteenDegreeTwoAlgebra.DegreeTwoLattice) :
    orderFourTwoBasis F R
        (orderFourReducedCentralFiberCoverHomologyDegreeTwo F x) =
      ![-(SphereSixComplex.alphaTwoMatrix *ᵥ x) 2,
        -(SphereSixComplex.alphaTwoMatrix *ᵥ x) 3] :=
  orderFour_projection_coordinates F R.orderFourTwo x

end EllipticFiniteCoverHomologyRealization

end SphereSixComplex.Topology.PaperAffineCyclicQuotientHomologyCoordinates
