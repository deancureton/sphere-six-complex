module

public import SphereSixComplex.Topology.ConnectedMayerVietorisDegreeZero
public import SphereSixComplex.Topology.PaperAffineCyclicQuotientHomologyCoordinates
public import SphereSixComplex.Topology.PaperEllipticFiniteCoverHomologyRealization
public import SphereSixComplex.Topology.PaperEllipticInteriorMayerVietorisBases

/-!
# Realizing the elliptic two-disc homology coordinates

This module turns the actual finite-cover calculations into the coordinate input for the
two-disc Mayer--Vietoris calculation.  The only extra datum is the naturality of the chosen
band trivializations: the order-three and order-four identifications of the same regular fibre
must induce the same period basis in degrees one and two.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Matrix Set
open scoped ContinuousMap

namespace SphereSixComplex

open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticFamilySpecialization
open Topology.PaperEllipticFillingRadialRetraction
open Topology.PaperEllipticReducedCentralFiberCoverModels
open Topology.PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData
open Topology.PaperAffineCyclicQuotientHomologyCoordinates
open LatticeData Topology.PaperLemmaSevenThirteenAlgebra

/-- Path connectedness is invariant under a homotopy equivalence. -/
public theorem pathConnectedSpace_of_homotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace Y] (e : X ≃ₕ Y) : PathConnectedSpace X := by
  refine
    { nonempty := ⟨e.invFun (Classical.choice (PathConnectedSpace.nonempty : Nonempty Y))⟩
      joined := ?_ }
  intro x y
  let H := e.left_inv.some
  have hx : Joined (e.invFun (e.toFun x)) x := ⟨H.evalAt x⟩
  have hy : Joined (e.invFun (e.toFun y)) y := ⟨H.evalAt y⟩
  have hxy : Joined (e.invFun (e.toFun x)) (e.invFun (e.toFun y)) :=
    (PathConnectedSpace.joined (e.toFun x) (e.toFun y)).map e.invFun.continuous
  exact hx.symm.trans (hxy.trans hy)

namespace Geometry.PaperAnalyticData

variable {A : PaperAnalyticData} {D : A.SectionSevenEllipticTwoDiscCoverData}

/-- The two trivializations of the regular band induce one common period basis.  This is the
precise naturality input needed to compare the two finite-cover projections; it contains no
Mayer--Vietoris matrix or homology computation of the union. -/
public structure EllipticBandHomologyAlignment
    (D : A.SectionSevenEllipticTwoDiscCoverData) : Prop where
  degreeOne : ∀ x : IntegralSingularHomology 1 (AdditiveTorus D.bandParameter),
    (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
        (integralSingularHomologyMap 1
          ⟨D.bandToOrderFourCoverSource, D.bandToOrderFourCoverSource.continuous⟩ x) =
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
        (integralSingularHomologyMap 1
          ⟨D.bandToOrderThreeCoverSource, D.bandToOrderThreeCoverSource.continuous⟩ x)
  degreeTwo : ∀ x : IntegralSingularHomology 2 (AdditiveTorus D.bandParameter),
    (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
        (integralSingularHomologyMap 2
          ⟨D.bandToOrderFourCoverSource, D.bandToOrderFourCoverSource.continuous⟩ x) =
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
        (integralSingularHomologyMap 2
          ⟨D.bandToOrderThreeCoverSource, D.bandToOrderThreeCoverSource.continuous⟩ x)

namespace EllipticBandHomologyAlignment

variable (R : EllipticFiniteCoverHomologyRealization A.periods)
  (N : A.EllipticBandHomologyAlignment D)

def finTwoProdFinTwoEquivFinFour :
    ((Fin 2 → ℤ) × (Fin 2 → ℤ)) ≃+ (Fin 4 → ℤ) where
  toFun x := ![x.1 0, x.1 1, x.2 0, x.2 1]
  invFun x := (![x 0, x 1], ![x 2, x 3])
  left_inv x := by
    rcases x with ⟨x, y⟩
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv x := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl

def bandOne :
    IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior) ≃+
      (Fin 4 → ℤ) :=
  (D.bandHomologyEquiv 1).trans <|
    (integralSingularHomologyEquiv 1 D.bandToOrderThreeCoverSource).trans
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne

def bandTwo :
    IntegralSingularHomology 2
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior) ≃+
      (Fin 6 → ℤ) :=
  (D.bandHomologyEquiv 2).trans <|
    (integralSingularHomologyEquiv 2 D.bandToOrderThreeCoverSource).trans
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo

def sidesOne :
    (IntegralSingularHomology 1 D.orderThreeSide ×
      IntegralSingularHomology 1 D.orderFourSide) ≃+ (Fin 4 → ℤ) :=
  (D.sideHomologyEquiv 1).trans <|
    ((R.orderThreeOneBasis A.periods).prodCongr (R.orderFourOneBasis A.periods)).trans
      finTwoProdFinTwoEquivFinFour

def sidesTwo :
    (IntegralSingularHomology 2 D.orderThreeSide ×
      IntegralSingularHomology 2 D.orderFourSide) ≃+ (Fin 4 → ℤ) :=
  (D.sideHomologyEquiv 2).trans <|
    ((R.orderThreeTwoBasis A.periods).prodCongr (R.orderFourTwoBasis A.periods)).trans
      finTwoProdFinTwoEquivFinFour

theorem integralHomologyMap_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (k : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularHomologyMap k (g.comp f) =
      (integralSingularHomologyMap k g).comp (integralSingularHomologyMap k f) := by
  ext x
  change ConcreteCategory.hom
      (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (g.comp f))) x = _
  rw [(show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g by rfl),
    Functor.map_comp]
  rfl

@[simp]
theorem integralHomologyEquiv_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) (e : X ≃ₜ Y) (x : IntegralSingularHomology k X) :
    integralSingularHomologyEquiv k e x = integralSingularHomologyMap k e x :=
  rfl

theorem orderThreeOne_projection (x : IntegralSingularHomology 1 (AdditiveTorus D.bandParameter)) :
    R.orderThreeOneBasis A.periods
        (integralSingularHomologyMap 1 D.orderThreeBandProjection x) =
      ![3 * gamma ((orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
          (integralSingularHomologyMap 1
            ⟨D.bandToOrderThreeCoverSource,
              D.bandToOrderThreeCoverSource.continuous⟩ x)),
        psiOne ((orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
          (integralSingularHomologyMap 1
            ⟨D.bandToOrderThreeCoverSource,
              D.bandToOrderThreeCoverSource.continuous⟩ x))] := by
  let y := (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
    (integralSingularHomologyMap 1
      ⟨D.bandToOrderThreeCoverSource, D.bandToOrderThreeCoverSource.continuous⟩ x)
  rw [show integralSingularHomologyMap 1 D.orderThreeBandProjection x =
      orderThreeReducedCentralFiberCoverHomologyDegreeOne A.periods y by
    rw [SectionSevenEllipticTwoDiscCoverData.orderThreeBandProjection,
      integralHomologyMap_comp]
    change (integralSingularHomologyMap 1 (centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)))
        (integralSingularHomologyMap 1
          ⟨D.bandToOrderThreeCoverSource,
            D.bandToOrderThreeCoverSource.continuous⟩ x) =
      (integralSingularHomologyMap 1 (centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)))
        ((orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne.symm y)
    rw [show (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne.symm y =
        integralSingularHomologyMap 1
          ⟨D.bandToOrderThreeCoverSource,
            D.bandToOrderThreeCoverSource.continuous⟩ x by
      exact (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne.symm_apply_apply _]]
  exact R.orderThreeOne_projection A.periods y

include N in
theorem orderFourOne_projection (x : IntegralSingularHomology 1 (AdditiveTorus D.bandParameter)) :
    R.orderFourOneBasis A.periods
        (integralSingularHomologyMap 1 D.orderFourBandProjection x) =
      ![4 * gamma ((orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
          (integralSingularHomologyMap 1
            ⟨D.bandToOrderThreeCoverSource,
              D.bandToOrderThreeCoverSource.continuous⟩ x)),
        psiTwo ((orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
          (integralSingularHomologyMap 1
            ⟨D.bandToOrderThreeCoverSource,
              D.bandToOrderThreeCoverSource.continuous⟩ x))] := by
  let y := (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
    (integralSingularHomologyMap 1
      ⟨D.bandToOrderFourCoverSource, D.bandToOrderFourCoverSource.continuous⟩ x)
  rw [show integralSingularHomologyMap 1 D.orderFourBandProjection x =
      orderFourReducedCentralFiberCoverHomologyDegreeOne A.periods y by
    rw [SectionSevenEllipticTwoDiscCoverData.orderFourBandProjection,
      integralHomologyMap_comp]
    change (integralSingularHomologyMap 1 (centralFiberCoverProjection
        (orderFourRadialActionData A.periods)))
        (integralSingularHomologyMap 1
          ⟨D.bandToOrderFourCoverSource,
            D.bandToOrderFourCoverSource.continuous⟩ x) =
      (integralSingularHomologyMap 1 (centralFiberCoverProjection
        (orderFourRadialActionData A.periods)))
        ((orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeOne.symm y)
    rw [show (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeOne.symm y =
        integralSingularHomologyMap 1
          ⟨D.bandToOrderFourCoverSource,
            D.bandToOrderFourCoverSource.continuous⟩ x by
      exact (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeOne.symm_apply_apply _]]
  rw [R.orderFourOne_projection A.periods y]
  have h := EllipticBandHomologyAlignment.degreeOne N x
  change y = _ at h
  rw [h]

theorem orderThreeTwo_projection (x : IntegralSingularHomology 2 (AdditiveTorus D.bandParameter)) :
    R.orderThreeTwoBasis A.periods
        (integralSingularHomologyMap 2 D.orderThreeBandProjection x) =
      fun i ↦ (alphaTwoMatrix *ᵥ
        ((orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
          (integralSingularHomologyMap 2
            ⟨D.bandToOrderThreeCoverSource,
              D.bandToOrderThreeCoverSource.continuous⟩ x))) (Fin.castAdd 2 i) := by
  let y := (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
    (integralSingularHomologyMap 2
      ⟨D.bandToOrderThreeCoverSource, D.bandToOrderThreeCoverSource.continuous⟩ x)
  rw [show integralSingularHomologyMap 2 D.orderThreeBandProjection x =
      orderThreeReducedCentralFiberCoverHomologyDegreeTwo A.periods y by
    rw [SectionSevenEllipticTwoDiscCoverData.orderThreeBandProjection,
      integralHomologyMap_comp]
    change (integralSingularHomologyMap 2 (centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)))
        (integralSingularHomologyMap 2
          ⟨D.bandToOrderThreeCoverSource,
            D.bandToOrderThreeCoverSource.continuous⟩ x) =
      (integralSingularHomologyMap 2 (centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)))
        ((orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo.symm y)
    rw [show (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo.symm y =
        integralSingularHomologyMap 2
          ⟨D.bandToOrderThreeCoverSource,
            D.bandToOrderThreeCoverSource.continuous⟩ x by
      exact (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo.symm_apply_apply _]]
  rw [R.orderThreeTwo_projection A.periods y]
  funext i
  fin_cases i <;> rfl

include N in
theorem orderFourTwo_projection (x : IntegralSingularHomology 2 (AdditiveTorus D.bandParameter)) :
    R.orderFourTwoBasis A.periods
        (integralSingularHomologyMap 2 D.orderFourBandProjection x) =
      fun i ↦ -(alphaTwoMatrix *ᵥ
        ((orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
          (integralSingularHomologyMap 2
            ⟨D.bandToOrderThreeCoverSource,
              D.bandToOrderThreeCoverSource.continuous⟩ x))) (Fin.natAdd 2 i) := by
  let y := (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
    (integralSingularHomologyMap 2
      ⟨D.bandToOrderFourCoverSource, D.bandToOrderFourCoverSource.continuous⟩ x)
  rw [show integralSingularHomologyMap 2 D.orderFourBandProjection x =
      orderFourReducedCentralFiberCoverHomologyDegreeTwo A.periods y by
    rw [SectionSevenEllipticTwoDiscCoverData.orderFourBandProjection,
      integralHomologyMap_comp]
    change (integralSingularHomologyMap 2 (centralFiberCoverProjection
        (orderFourRadialActionData A.periods)))
        (integralSingularHomologyMap 2
          ⟨D.bandToOrderFourCoverSource,
            D.bandToOrderFourCoverSource.continuous⟩ x) =
      (integralSingularHomologyMap 2 (centralFiberCoverProjection
        (orderFourRadialActionData A.periods)))
        ((orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo.symm y)
    rw [show (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo.symm y =
        integralSingularHomologyMap 2
          ⟨D.bandToOrderFourCoverSource,
            D.bandToOrderFourCoverSource.continuous⟩ x by
      exact (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo.symm_apply_apply _]]
  rw [R.orderFourTwo_projection A.periods y]
  have h := EllipticBandHomologyAlignment.degreeTwo N x
  change y = _ at h
  rw [h]
  funext i
  fin_cases i <;> rfl

include N in
theorem differenceOne (x) :
    sidesOne R
        (IntegralMayerVietoris.differenceMap
          D.orderThreeSide D.orderFourSide 1 x) =
      ellipticActualHOneDifferenceMatrix *ᵥ bandOne (D := D) x := by
  rw [show sidesOne R
      (IntegralMayerVietoris.differenceMap D.orderThreeSide D.orderFourSide 1 x) =
      finTwoProdFinTwoEquivFinFour
        ((R.orderThreeOneBasis A.periods).prodCongr (R.orderFourOneBasis A.periods)
          (D.sideHomologyEquiv 1
            (IntegralMayerVietoris.differenceMap
              D.orderThreeSide D.orderFourSide 1 x))) by rfl]
  rw [D.differenceMap_one_conjugacy]
  change ![
      R.orderThreeOneBasis A.periods
        (integralSingularHomologyMap 1 D.orderThreeBandProjection
          (D.bandHomologyEquiv 1 x)) 0,
      R.orderThreeOneBasis A.periods
        (integralSingularHomologyMap 1 D.orderThreeBandProjection
          (D.bandHomologyEquiv 1 x)) 1,
      R.orderFourOneBasis A.periods
        (-integralSingularHomologyMap 1 D.orderFourBandProjection
          (D.bandHomologyEquiv 1 x)) 0,
      R.orderFourOneBasis A.periods
        (-integralSingularHomologyMap 1 D.orderFourBandProjection
          (D.bandHomologyEquiv 1 x)) 1] = _
  rw [map_neg]
  rw [orderThreeOne_projection R, orderFourOne_projection R N]
  let y := (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
    (integralSingularHomologyMap 1
      ⟨D.bandToOrderThreeCoverSource, D.bandToOrderThreeCoverSource.continuous⟩
      (D.bandHomologyEquiv 1 x))
  change ![3 * gamma y, psiOne y, -(4 * gamma y), -psiTwo y] =
    ellipticActualHOneDifferenceMatrix *ᵥ y
  funext i
  fin_cases i <;>
    simp [ellipticActualHOneDifferenceMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, gamma, psiOne, psiTwo] <;>
    ring

include N in
theorem differenceTwo (x) :
    sidesTwo R
        (IntegralMayerVietoris.differenceMap
          D.orderThreeSide D.orderFourSide 2 x) =
      alphaTwoMatrix *ᵥ bandTwo (D := D) x := by
  rw [show sidesTwo R
      (IntegralMayerVietoris.differenceMap D.orderThreeSide D.orderFourSide 2 x) =
      finTwoProdFinTwoEquivFinFour
        ((R.orderThreeTwoBasis A.periods).prodCongr (R.orderFourTwoBasis A.periods)
          (D.sideHomologyEquiv 2
            (IntegralMayerVietoris.differenceMap
              D.orderThreeSide D.orderFourSide 2 x))) by rfl]
  rw [D.differenceMap_two_conjugacy]
  change ![
      R.orderThreeTwoBasis A.periods
        (integralSingularHomologyMap 2 D.orderThreeBandProjection
          (D.bandHomologyEquiv 2 x)) 0,
      R.orderThreeTwoBasis A.periods
        (integralSingularHomologyMap 2 D.orderThreeBandProjection
          (D.bandHomologyEquiv 2 x)) 1,
      R.orderFourTwoBasis A.periods
        (-integralSingularHomologyMap 2 D.orderFourBandProjection
          (D.bandHomologyEquiv 2 x)) 0,
      R.orderFourTwoBasis A.periods
        (-integralSingularHomologyMap 2 D.orderFourBandProjection
          (D.bandHomologyEquiv 2 x)) 1] = _
  rw [map_neg]
  rw [orderThreeTwo_projection R, orderFourTwo_projection R N]
  let y := (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeTwo
    (integralSingularHomologyMap 2
      ⟨D.bandToOrderThreeCoverSource, D.bandToOrderThreeCoverSource.continuous⟩
      (D.bandHomologyEquiv 2 x))
  change ![(alphaTwoMatrix *ᵥ y) 0, (alphaTwoMatrix *ᵥ y) 1,
    -(-(alphaTwoMatrix *ᵥ y) 2), -(-(alphaTwoMatrix *ᵥ y) 3)] =
      alphaTwoMatrix *ᵥ y
  funext i
  fin_cases i <;> simp

theorem centralFiberCoverProjection_surjective
    {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] [AddCommGroup T]
    (E : RadialEllipticActionData m T) :
    Function.Surjective (centralFiberCoverProjection E) := by
  rintro ⟨x, hx⟩
  rcases hx with ⟨p, hp, rfl⟩
  exact ⟨⟨p, ⟨p, hp, rfl⟩⟩, rfl⟩

theorem differenceZero_injective : Function.Injective
    (IntegralMayerVietoris.differenceMap D.orderThreeSide D.orderFourSide 0) := by
  let E₃ := orderThreeRadialActionData A.periods
  let E₄ := orderFourRadialActionData A.periods
  let _ : PathConnectedSpace
      (centralFiberCoverSource E₃) :=
    (centralFiberCoverSourceHomeomorph E₃).symm.surjective.pathConnectedSpace
      (centralFiberCoverSourceHomeomorph E₃).symm.continuous
  let _ : PathConnectedSpace
      (centralFiberCoverSource E₄) :=
    (centralFiberCoverSourceHomeomorph E₄).symm.surjective.pathConnectedSpace
      (centralFiberCoverSourceHomeomorph E₄).symm.continuous
  let _ : PathConnectedSpace (OrderThreeReducedCentralFiber A.periods) :=
    (centralFiberCoverProjection_surjective E₃).pathConnectedSpace
      (centralFiberCoverProjection E₃).continuous
  let _ : PathConnectedSpace (OrderFourReducedCentralFiber A.periods) :=
    (centralFiberCoverProjection_surjective E₄).pathConnectedSpace
      (centralFiberCoverProjection E₄).continuous
  let _ : PathConnectedSpace D.orderThreeSide :=
    pathConnectedSpace_of_homotopyEquiv D.orderThreeSideHomotopyEquiv
  let _ : PathConnectedSpace D.orderFourSide :=
    pathConnectedSpace_of_homotopyEquiv D.orderFourSideHomotopyEquiv
  let _ : PathConnectedSpace
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior) :=
    pathConnectedSpace_of_homotopyEquiv D.bandHomotopyEquiv
  exact IntegralMayerVietoris.differenceMap_zero_injective _ _

/-- The band alignment and the four finite-cover computations construct all coordinate data
needed for the elliptic-interior Mayer--Vietoris calculation. -/
public noncomputable def homologyCoordinates :
    A.SectionSevenEllipticTwoDiscHomologyCoordinates D where
  bandOne := bandOne (D := D)
  sidesOne := sidesOne (D := D) R
  differenceOne := differenceOne (D := D) R N
  bandTwo := bandTwo (D := D)
  sidesTwo := sidesTwo (D := D) R
  differenceTwo := differenceTwo (D := D) R N
  differenceZero_injective := differenceZero_injective

/-- The actual finite-cover realization leaves only band-basis naturality as input to the
elliptic-interior Mayer--Vietoris coordinates. -/
public noncomputable def actualHomologyCoordinates :
    A.SectionSevenEllipticTwoDiscHomologyCoordinates D :=
  homologyCoordinates (D := D)
    (Topology.FiniteCoverPerfectPairing.ellipticFiniteCoverHomologyRealization A.periods) N

end EllipticBandHomologyAlignment

end Geometry.PaperAnalyticData

end SphereSixComplex
