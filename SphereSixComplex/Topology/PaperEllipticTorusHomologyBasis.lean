module

public import SphereSixComplex.Geometry.EllipticActualActionTopology
public import SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels
public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasisProof

/-!
# Integral homology bases for the elliptic period tori

This file gives the standard integral degree-one and degree-two models of a full-rank period
torus.  The degree-two action is defined by the actual second compound matrix.  The bases
themselves are constructed in `PaperEllipticTorusHomologyBasisProof`; the only missing topology
input is their naturality under descended affine automorphisms.
-/

open AlgebraicTopology Matrix Set
open scoped ContinuousMap

namespace SphereSixComplex

open LatticeData Periods TriangleGroup
open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticActualActionTopology Geometry.EllipticFamilySpecialization
open Geometry.GlobalTorusFamily

noncomputable section

/-- First coordinate in the ordered list `(01, 02, 03, 12, 13, 23)`. -/
@[expose] public def periodPairFirst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

/-- Second coordinate in the ordered list `(01, 02, 03, 12, 13, 23)`. -/
@[expose] public def periodPairSecond : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

public theorem periodPairFirst_lt_second (i : Fin 6) :
    periodPairFirst i < periodPairSecond i := by
  fin_cases i <;> decide

/-- The second compound of a four-by-four matrix in coordinates `(01, 02, 03, 12, 13, 23)`. -/
@[expose] public def secondCompoundMatrix
    (M : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun ij ab ↦
    M (periodPairFirst ij) (periodPairFirst ab) *
        M (periodPairSecond ij) (periodPairSecond ab) -
      M (periodPairFirst ij) (periodPairSecond ab) *
        M (periodPairSecond ij) (periodPairFirst ab)

/-- Matrix of the induced action on exterior degree two, in the six increasing-pair
coordinates. -/
@[expose] public def exteriorSquareMatrix
    (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) : Matrix (Fin 6) (Fin 6) ℤ :=
  secondCompoundMatrix (LinearMap.toMatrix' e.toLinearMap)

/-- The degree-two map associated to an integral automorphism of the period lattice. -/
@[expose] public def exteriorSquareMap
    (e : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods) : (Fin 6 → ℤ) →+ (Fin 6 → ℤ) :=
  (Matrix.toLin' (exteriorSquareMatrix e)).toAddHom

public theorem integralMatrix_rhoLambda_gOne :
    LinearMap.toMatrix' (rhoLambda g₁).toLinearMap = A₁ := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  convert congrFun (rhoLambda_g₁_apply (Pi.single j 1)) i using 1 <;> simp

public theorem integralMatrix_rhoLambda_gTwo :
    LinearMap.toMatrix' (rhoLambda g₂).toLinearMap = A₂ := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  convert congrFun (rhoLambda_g₂_apply (Pi.single j 1)) i using 1 <;> simp

/-- The degree-two order-three action is the second compound of the source matrix `A₁`. -/
public theorem exteriorSquareMatrix_rhoLambda_gOne :
    exteriorSquareMatrix (rhoLambda g₁) =
      secondCompoundMatrix A₁ := by
  rw [exteriorSquareMatrix, integralMatrix_rhoLambda_gOne]

/-- The degree-two order-four action is the second compound of the source matrix `A₂`. -/
public theorem exteriorSquareMatrix_rhoLambda_gTwo :
    exteriorSquareMatrix (rhoLambda g₂) =
      secondCompoundMatrix A₂ := by
  rw [exteriorSquareMatrix, integralMatrix_rhoLambda_gTwo]

/-- An affine automorphism of a period torus together with its actual lift and integral lattice
automorphism. -/
public structure DescendedAffineTorusAutomorphism (p : SphereSixComplex.Periods.Parameters) where
  latticeMap : IntegerPeriods ≃ₗ[ℤ] IntegerPeriods
  lift : ComplexTwoSpace ≃+ ComplexTwoSpace
  lift_period : ∀ n, lift (periodVector p n) = periodVector p (latticeMap n)
  translation : AdditiveTorus p
  map : C(AdditiveTorus p, AdditiveTorus p)
  map_mk : ∀ z, map (Quotient.mk _ z) = Quotient.mk _ (lift z) + translation

/-- Integral degree-one and degree-two bases with the ranks of a four-torus. -/
public structure FourTorusHomologyBasis (X : Type) [TopologicalSpace X] where
  degreeOne : IntegralSingularHomology 1 X ≃+ (Fin 4 → ℤ)
  degreeTwo : IntegralSingularHomology 2 X ≃+ (Fin 6 → ℤ)

/-- The standard integral bases of the first two homology groups of a full-rank complex
two-torus. -/
public abbrev AdditiveTorusHomologyBasis
    (p : SphereSixComplex.Periods.Parameters) := FourTorusHomologyBasis (AdditiveTorus p)

namespace FourTorusHomologyBasis

variable {p : SphereSixComplex.Periods.Parameters} {X : Type} [TopologicalSpace X]

/-- Transport the standard torus bases to a homeomorphic presentation. -/
@[expose] public def homeomorph (B : AdditiveTorusHomologyBasis p)
    (e : X ≃ₜ AdditiveTorus p) :
    FourTorusHomologyBasis X where
  degreeOne := (integralSingularHomologyEquiv 1 e).trans B.degreeOne
  degreeTwo := (integralSingularHomologyEquiv 2 e).trans B.degreeTwo

end FourTorusHomologyBasis

namespace EstablishedTorusHomology

/-- The integral singular homology of a full-rank complex two-torus, in the period basis.  This
is the standard circle-product and Kunneth calculation, carried out in
`PaperEllipticTorusHomologyBasisProof` by iterating the Wang sequence of the mapping torus of an
identity map. -/
@[expose] public def additiveTorusHomologyBasis
    (p : SphereSixComplex.Periods.Parameters) (hfull : FullRank p) :
    AdditiveTorusHomologyBasis p where
  degreeOne := StandardTorusHomology.additiveTorusHomologyDegreeOne p hfull
  degreeTwo := StandardTorusHomology.additiveTorusHomologyDegreeTwo p hfull

/-- The two components of the basis.  `additiveTorusHomologyDegreeOne` and
`additiveTorusHomologyDegreeTwo` are deliberately not exposed, so downstream modules see the
basis exactly as opaquely as they saw the axiom this definition replaced. -/
public theorem additiveTorusHomologyBasis_degreeOne
    (p : SphereSixComplex.Periods.Parameters) (hfull : FullRank p) :
    (additiveTorusHomologyBasis p hfull).degreeOne =
      StandardTorusHomology.additiveTorusHomologyDegreeOne p hfull := rfl

public theorem additiveTorusHomologyBasis_degreeTwo
    (p : SphereSixComplex.Periods.Parameters) (hfull : FullRank p) :
    (additiveTorusHomologyBasis p hfull).degreeTwo =
      StandardTorusHomology.additiveTorusHomologyDegreeTwo p hfull := rfl

/-- Naturality of the standard torus bases under a descended affine automorphism.  Translation
acts trivially, the degree-one map is the integral lattice map, and degree two is its exterior
square.

This is the one remaining input.  The bases of `additiveTorusHomologyBasis` are produced by an
iterated Wang splitting, whose sections are chosen by projectivity rather than geometrically, so
they carry no relation to the period lattice; deriving this statement requires the natural
identification `H₁(V/Λ) ≃ Λ` (and its exterior square in degree two), which the Wang
route does not supply. -/
public axiom additiveTorusHomologyBasis_naturality
    (p : SphereSixComplex.Periods.Parameters) (hfull : FullRank p)
    (D : DescendedAffineTorusAutomorphism p) :
    let B := additiveTorusHomologyBasis p hfull
    (∀ x, B.degreeOne (integralSingularHomologyMap 1 D.map x) =
      D.latticeMap (B.degreeOne x)) ∧
    (∀ x, B.degreeTwo (integralSingularHomologyMap 2 D.map x) =
      exteriorSquareMap D.latticeMap (B.degreeTwo x))

end EstablishedTorusHomology

namespace Geometry.EllipticFamilySpecialization

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The order-three affine fibre generator, with its exact integral period-lattice action. -/
@[expose] public def orderThreeDescendedAffineTorusAutomorphism :
    DescendedAffineTorusAutomorphism (parameterMap F U.zOne).1 where
  latticeMap := rhoLambda g₁
  lift := (periodTransport g₁ (parameterMap F U.zOne)).toAddEquiv
  lift_period n := by
    change periodTransport g₁ (parameterMap F U.zOne)
      (periodVector (parameterMap F U.zOne).1 n) = _
    simpa only [parameterMap_zOne_fixed F] using
      periodTransport_periodVector g₁ (parameterMap F U.zOne) n
  translation := orderThreeTranslation (parameterMap F U.zOne).1
  map :=
    ⟨fun q ↦ orderThreeFiberAutomorphism F q +
        orderThreeTranslation (parameterMap F U.zOne).1,
      (orderThreeFiberAutomorphism_continuous F).add continuous_const⟩
  map_mk z := by
    change orderThreeFiberAutomorphism F (Quotient.mk _ z) + _ = _
    rw [orderThreeFiberAutomorphism_mk]
    rfl

/-- The order-four affine fibre generator, with its exact integral period-lattice action. -/
@[expose] public def orderFourDescendedAffineTorusAutomorphism :
    DescendedAffineTorusAutomorphism (parameterMap F U.zTwo).1 where
  latticeMap := rhoLambda g₂
  lift := (periodTransport g₂ (parameterMap F U.zTwo)).toAddEquiv
  lift_period n := by
    change periodTransport g₂ (parameterMap F U.zTwo)
      (periodVector (parameterMap F U.zTwo).1 n) = _
    simpa only [parameterMap_zTwo_fixed F] using
      periodTransport_periodVector g₂ (parameterMap F U.zTwo) n
  translation := orderFourTranslation (parameterMap F U.zTwo).1
  map :=
    ⟨fun q ↦ orderFourFiberAutomorphism F q +
        orderFourTranslation (parameterMap F U.zTwo).1,
      (orderFourFiberAutomorphism_continuous F).add continuous_const⟩
  map_mk z := by
    change orderFourFiberAutomorphism F (Quotient.mk _ z) + _ = _
    rw [orderFourFiberAutomorphism_mk]
    rfl

/-- Standard homology bases of the actual order-three central four-torus. -/
@[expose] public def orderThreeTorusHomologyBasis :
    AdditiveTorusHomologyBasis (parameterMap F U.zOne).1 :=
  EstablishedTorusHomology.additiveTorusHomologyBasis _
    (fullRankDomain (parameterMap F U.zOne))

/-- Standard homology bases of the actual order-four central four-torus. -/
@[expose] public def orderFourTorusHomologyBasis :
    AdditiveTorusHomologyBasis (parameterMap F U.zTwo).1 :=
  EstablishedTorusHomology.additiveTorusHomologyBasis _
    (fullRankDomain (parameterMap F U.zTwo))

/-- In the standard degree-one basis, the order-three affine generator acts by the actual
integral monodromy `rhoLambda g₁`. -/
public theorem orderThreeFiberGenerator_homology_degreeOne (x) :
    (orderThreeTorusHomologyBasis F).degreeOne
        (integralSingularHomologyMap 1
          (orderThreeDescendedAffineTorusAutomorphism F).map x) =
      rhoLambda g₁ ((orderThreeTorusHomologyBasis F).degreeOne x) :=
  (EstablishedTorusHomology.additiveTorusHomologyBasis_naturality _
    (fullRankDomain (parameterMap F U.zOne))
    (orderThreeDescendedAffineTorusAutomorphism F)).1 x

/-- In degree two, the order-three affine generator acts by the second compound matrix of its
actual integral monodromy. -/
public theorem orderThreeFiberGenerator_homology_degreeTwo (x) :
    (orderThreeTorusHomologyBasis F).degreeTwo
        (integralSingularHomologyMap 2
          (orderThreeDescendedAffineTorusAutomorphism F).map x) =
      exteriorSquareMap (rhoLambda g₁) ((orderThreeTorusHomologyBasis F).degreeTwo x) :=
  (EstablishedTorusHomology.additiveTorusHomologyBasis_naturality _
    (fullRankDomain (parameterMap F U.zOne))
    (orderThreeDescendedAffineTorusAutomorphism F)).2 x

/-- In the standard degree-one basis, the order-four affine generator acts by the actual
integral monodromy `rhoLambda g₂`. -/
public theorem orderFourFiberGenerator_homology_degreeOne (x) :
    (orderFourTorusHomologyBasis F).degreeOne
        (integralSingularHomologyMap 1
          (orderFourDescendedAffineTorusAutomorphism F).map x) =
      rhoLambda g₂ ((orderFourTorusHomologyBasis F).degreeOne x) :=
  (EstablishedTorusHomology.additiveTorusHomologyBasis_naturality _
    (fullRankDomain (parameterMap F U.zTwo))
    (orderFourDescendedAffineTorusAutomorphism F)).1 x

/-- In degree two, the order-four affine generator acts by the second compound matrix of its
actual integral monodromy. -/
public theorem orderFourFiberGenerator_homology_degreeTwo (x) :
    (orderFourTorusHomologyBasis F).degreeTwo
        (integralSingularHomologyMap 2
          (orderFourDescendedAffineTorusAutomorphism F).map x) =
      exteriorSquareMap (rhoLambda g₂) ((orderFourTorusHomologyBasis F).degreeTwo x) :=
  (EstablishedTorusHomology.additiveTorusHomologyBasis_naturality _
    (fullRankDomain (parameterMap F U.zTwo))
    (orderFourDescendedAffineTorusAutomorphism F)).2 x

end Geometry.EllipticFamilySpecialization

namespace Topology.PaperEllipticReducedCentralFiberCoverModels

open Geometry.EllipticFamilySpecialization
open Topology.PaperEllipticFillingRadialRetraction

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The source of the order-three reduced-fibre covering has the standard four-torus homology
bases. -/
@[expose] public def orderThreeCentralFiberCoverSourceHomologyBasis :
    FourTorusHomologyBasis
      (RadialEllipticActionData.centralFiberCoverSource (orderThreeRadialActionData F)) :=
  (orderThreeTorusHomologyBasis F).homeomorph
    (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
      (orderThreeRadialActionData F))

/-- The source of the order-four reduced-fibre covering has the standard four-torus homology
bases. -/
@[expose] public def orderFourCentralFiberCoverSourceHomologyBasis :
    FourTorusHomologyBasis
      (RadialEllipticActionData.centralFiberCoverSource (orderFourRadialActionData F)) :=
  (orderFourTorusHomologyBasis F).homeomorph
    (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
      (orderFourRadialActionData F))

/-- The actual order-three covering map on first homology, with its source written in the
standard period basis. -/
@[expose] public def orderThreeReducedCentralFiberCoverHomologyDegreeOne :
    (Fin 4 → ℤ) →+ IntegralSingularHomology 1 (OrderThreeReducedCentralFiber F) :=
  (integralSingularHomologyMap 1
    (RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData F))).comp
    (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeOne.symm.toAddHom

/-- The actual order-three covering map on second homology, with its source written in exterior
degree-two period coordinates. -/
@[expose] public def orderThreeReducedCentralFiberCoverHomologyDegreeTwo :
    (Fin 6 → ℤ) →+ IntegralSingularHomology 2 (OrderThreeReducedCentralFiber F) :=
  (integralSingularHomologyMap 2
    (RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData F))).comp
    (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm.toAddHom

/-- The actual order-four covering map on first homology, with its source written in the
standard period basis. -/
@[expose] public def orderFourReducedCentralFiberCoverHomologyDegreeOne :
    (Fin 4 → ℤ) →+ IntegralSingularHomology 1 (OrderFourReducedCentralFiber F) :=
  (integralSingularHomologyMap 1
    (RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData F))).comp
    (orderFourCentralFiberCoverSourceHomologyBasis F).degreeOne.symm.toAddHom

/-- The actual order-four covering map on second homology, with its source written in exterior
degree-two period coordinates. -/
@[expose] public def orderFourReducedCentralFiberCoverHomologyDegreeTwo :
    (Fin 6 → ℤ) →+ IntegralSingularHomology 2 (OrderFourReducedCentralFiber F) :=
  (integralSingularHomologyMap 2
    (RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData F))).comp
    (orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm.toAddHom

end Topology.PaperEllipticReducedCentralFiberCoverModels

end

end SphereSixComplex
