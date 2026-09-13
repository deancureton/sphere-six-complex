module

public import SphereSixComplex.Paper.Topology.PaperEllipticFiniteCoverHomologyRealization
public import SphereSixComplex.Paper.Topology.PaperEllipticInteriorMayerVietorisBases
public import SphereSixComplex.Prerequisites.Topology.NormalizedWangHomologySplitting

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory Matrix Set
open scoped ContinuousMap
namespace SphereSixComplex
open Geometry Geometry.AnalyticTorusFamily Geometry.ComplexTorus
open Geometry.EllipticFamilySpecialization
open EllipticFilling EllipticFilling.RadialEllipticActionData
open AffineCyclicQuotientHomology LatticeData MultipleFiberCoinvariants
namespace Geometry.AnalyticData.EllipticHomologyOne
variable {A : AnalyticData} {D : A.EllipticTwoDiscCoverData}

variable (hAlignment : ∀ x : IntegralSingularHomology 1 (AdditiveTorus D.bandParameter),
    (orderFourCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
      (integralSingularHomologyMap 1 D.bandToOrderFourCoverSource x) =
    (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
      (integralSingularHomologyMap 1 D.bandToOrderThreeCoverSource x))

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
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior) ≃+
      (Fin 4 → ℤ) :=
  (D.bandHomologyEquiv 1).trans <|
    (integralSingularHomologyEquiv 1 D.bandToOrderThreeCoverSource).trans
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne

def sidesOne :
    (IntegralSingularHomology 1 D.orderThreeSide ×
      IntegralSingularHomology 1 D.orderFourSide) ≃+ (Fin 4 → ℤ) :=
  (D.sideHomologyEquiv 1).trans <|
    (((orderThreeReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv).prodCongr ((orderFourReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv)).trans
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
    (orderThreeReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv
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
    rw [EllipticTwoDiscCoverData.orderThreeBandProjection,
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
  exact Topology.FiniteCoverPerfectPairing.orderThreeHOneNaturality A.periods y

include hAlignment in
theorem orderFourOne_projection (x : IntegralSingularHomology 1 (AdditiveTorus D.bandParameter)) :
    (orderFourReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv
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
    rw [EllipticTwoDiscCoverData.orderFourBandProjection,
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
  erw [Topology.FiniteCoverPerfectPairing.orderFourHOneNaturality A.periods y]
  have h := hAlignment x
  change y = _ at h
  rw [h]
  rfl

theorem bandOne_apply (x) :
    bandOne (D := D) x =
      (orderThreeCentralFiberCoverSourceHomologyBasis A.periods).degreeOne
        (integralSingularHomologyMap 1
          ⟨D.bandToOrderThreeCoverSource, D.bandToOrderThreeCoverSource.continuous⟩
          (D.bandHomologyEquiv 1 x)) := by
  unfold bandOne
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, integralHomologyEquiv_apply]

theorem orderThreeOne_projection_bandOne (x) :
    (orderThreeReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv
        (integralSingularHomologyMap 1 D.orderThreeBandProjection
          (D.bandHomologyEquiv 1 x)) =
      ![3 * gamma (bandOne (D := D) x), psiOne (bandOne (D := D) x)] := by
  rw [orderThreeOne_projection]
  rw [bandOne_apply]

include hAlignment in
theorem orderFourOne_projection_bandOne (x) :
    (orderFourReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv
        (integralSingularHomologyMap 1 D.orderFourBandProjection
          (D.bandHomologyEquiv 1 x)) =
      ![4 * gamma (bandOne (D := D) x), psiTwo (bandOne (D := D) x)] := by
  rw [orderFourOne_projection hAlignment]
  rw [bandOne_apply]

include hAlignment in
theorem differenceOne (x) :
    sidesOne (D := D)
        (IntegralMayerVietoris.differenceMap
          D.orderThreeSide D.orderFourSide 1 x) =
      ellipticActualHOneDifferenceMatrix *ᵥ bandOne (D := D) x := by
  rw [show sidesOne (D := D)
      (IntegralMayerVietoris.differenceMap D.orderThreeSide D.orderFourSide 1 x) =
      finTwoProdFinTwoEquivFinFour
        (((orderThreeReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv).prodCongr ((orderFourReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv)
          (D.sideHomologyEquiv 1
            (IntegralMayerVietoris.differenceMap
              D.orderThreeSide D.orderFourSide 1 x))) by rfl]
  rw [D.differenceMap_one_conjugacy]
  change ![
      (orderThreeReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv
        (integralSingularHomologyMap 1 D.orderThreeBandProjection
          (D.bandHomologyEquiv 1 x)) 0,
      (orderThreeReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv
        (integralSingularHomologyMap 1 D.orderThreeBandProjection
          (D.bandHomologyEquiv 1 x)) 1,
      (orderFourReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv
        (-integralSingularHomologyMap 1 D.orderFourBandProjection
          (D.bandHomologyEquiv 1 x)) 0,
      (orderFourReducedCentralFiberHOneEquivIntSquared A.periods).toAddEquiv
        (-integralSingularHomologyMap 1 D.orderFourBandProjection
          (D.bandHomologyEquiv 1 x)) 1] = _
  rw [map_neg]
  rw [orderThreeOne_projection_bandOne, orderFourOne_projection_bandOne hAlignment]
  funext i
  fin_cases i <;>
    simp [ellipticActualHOneDifferenceMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, gamma, psiOne, psiTwo] <;>
    ring

include hAlignment in
theorem differenceOne_linear_comm :
    (sidesOne (D := D)).toIntLinearEquiv.toLinearMap.comp
      (IntegralMayerVietoris.differenceMap D.orderThreeSide D.orderFourSide 1).toIntLinearMap =
    ellipticActualHOneLinear.comp (bandOne (D := D)).toIntLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact differenceOne hAlignment x

include hAlignment in
theorem kernel_iff (x) :
    IntegralMayerVietoris.differenceMap D.orderThreeSide D.orderFourSide 1 x = 0 ↔
      ∃ t : ℤ, bandOne (D := D) x = t • alphaOneKernelGenerator := by
  rw [← ellipticActualHOne_kernel, ← differenceOne hAlignment]
  exact (sidesOne (D := D)).map_eq_zero_iff.symm

theorem differenceMap_zero_injective : Function.Injective
    (IntegralMayerVietoris.differenceMap D.orderThreeSide D.orderFourSide 0) := by
  let e := D.bandHomotopyEquiv
  let : PathConnectedSpace (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior) := by
    refine { nonempty := ⟨e.invFun (Classical.choice inferInstance)⟩, joined := ?_ }
    intro x y
    let H := e.left_inv.some
    exact (show Joined (e.invFun (e.toFun x)) x from ⟨H.evalAt x⟩).symm.trans
      (((PathConnectedSpace.joined (e.toFun x) (e.toFun y)).map e.invFun.continuous).trans
        (show Joined (e.invFun (e.toFun y)) y from ⟨H.evalAt y⟩))
  exact IntegralMayerVietoris.differenceMap_zero_injective _ _

open EllipticTwoDiscHomologyCoordinates
/-- The degree-one fibre-cokernel coordinate. -/
public noncomputable def degreeOneCoinvariantEquiv :
    (presentationOne (D := D)).Coinvariants ≃ₗ[ℤ] ℤ :=
  (cokernelEquivOfComm (bandOne (D := D)).toIntLinearEquiv (sidesOne (D := D)).toIntLinearEquiv
    (presentationOne (D := D)).highDifference.toIntLinearMap ellipticActualHOneLinear
      (differenceOne_linear_comm hAlignment)).trans ellipticActualHOneCokernelEquivInt

/-- Degree zero has no invariant term because the two sides and their overlap are connected. -/
public def degreeOneInvariantEquiv :
    (presentationOne (D := D)).invariants ≃ₗ[ℤ] (Fin 0 → ℤ) :=
  kernelEquivFinZeroOfInjective
    (presentationOne (D := D)).lowDifference.toIntLinearMap (differenceMap_zero_injective (D := D))

/-- The unique normalized splitting when the invariant term is zero. -/
public def degreeOneZeroSplitting :
    WangHomologyPresentation.NormalizedSplitting (presentationOne (D := D)) where
  sweptSection := 0
  rightInverse := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply,
      LinearMap.id_apply]
    apply (differenceMap_zero_injective (D := D))
    change (presentationOne (D := D)).lowDifference
        ((presentationOne (D := D)).boundary 0) =
      (presentationOne (D := D)).lowDifference x.1
    rw [(presentationOne (D := D)).lowDifference_boundary]
    exact (LinearMap.mem_ker.mp x.2).symm

/-- Canonical degree-one coordinates on the literal union of the two elliptic sides. -/
public noncomputable def normalizedUnionHomologyOneEquiv :
    IntegralSingularHomology 1
        (D.orderThreeSide ∪ D.orderFourSide : Set A.ellipticInterior) ≃+
      (Fin 1 → ℤ) :=
  ((WangHomologyPresentation.NormalizedSplitting.totalLinearEquivOfEndCoordinates
      (presentationOne (D := D)) (degreeOneZeroSplitting (D := D)) (degreeOneCoinvariantEquiv hAlignment)
      (degreeOneInvariantEquiv (D := D))).trans intProdFinZeroEquivFinOne).toAddEquiv

/-- Canonical degree-one coordinates on the actual elliptic interior. -/
public noncomputable def normalizedEllipticInteriorHomologyOneEquiv :
    IntegralSingularHomology 1 A.ellipticInterior ≃+ (Fin 1 → ℤ) := by
  let eTop := integralSingularHomologyEquiv 1
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.ellipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  exact eTop.symm.trans (normalizedUnionHomologyOneEquiv hAlignment)

end Geometry.AnalyticData.EllipticHomologyOne
end SphereSixComplex
