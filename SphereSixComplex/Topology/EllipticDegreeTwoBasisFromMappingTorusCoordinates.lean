module

public import SphereSixComplex.Topology.EllipticDegreeTwoCoinvariants
public import SphereSixComplex.Topology.FiniteCoverPerfectPairing
public import SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverCore
public import SphereSixComplex.Topology.PaperEllipticTorusHomologyBasis

/-!
# Elliptic degree-two bases from mapping-torus projection coordinates

This module separates the finite integral calculation in Proposition 7.14 from its remaining
topological naturality square.  Once coordinates on the two mapping-torus homology groups identify
the covering projections with the already computed coinvariant maps, the displayed bases and the
order-four index-two relation follow formally.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix

namespace SphereSixComplex.Topology.EllipticDegreeTwoBasisFromMappingTorusCoordinates

open Geometry Geometry.EllipticFamilySpecialization
open EllipticDegreeTwoCoinvariants FiniteCoverPerfectPairing
open PaperEllipticFillingRadialRetraction
open PaperEllipticReducedCentralFiberCoverModels
open PaperPropositionSevenFourteenDegreeTwoAlgebra

variable {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)

/-- The exact naturality square left after the two finite deck-coinvariant calculations.

The two equivalences can be constructed from the Wang sequences of the explicit three-torus
mapping-torus models.  The two equations say that the original four-torus covering maps agree
with those Wang coordinates. -/
public structure ProjectionCoordinates where
  orderThree :
    IntegralSingularHomology 2 (OrderThreeReducedCentralFiber F) ≃+ (Fin 2 → ℤ)
  orderThree_projection : ∀ x : DegreeTwoLattice,
    orderThree
        (integralSingularHomologyMap 2
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderThreeRadialActionData F))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) =
      orderThreeCoverCoordinates (orderThreeCoinvariantCoordinates x)
  orderFour :
    IntegralSingularHomology 2 (OrderFourReducedCentralFiber F) ≃+ (Fin 2 → ℤ)
  orderFour_projection : ∀ x : DegreeTwoLattice,
    orderFour
        (integralSingularHomologyMap 2
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderFourRadialActionData F))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) =
      orderFourCoverCoordinates (orderFourCoinvariantCoordinates x)

namespace ProjectionCoordinates

public theorem orderThree_projected_one (P : ProjectionCoordinates F) :
    P.orderThree (orderThreeProjectedDegreeTwoGenerator F 1) = ![1, -2] := by
  rw [orderThreeProjectedDegreeTwoGenerator, P.orderThree_projection]
  funext i
  fin_cases i <;>
    simp [orderThreeCoinvariantCoordinates, orderThreeCoverCoordinates]

public theorem orderThree_projected_three (P : ProjectionCoordinates F) :
    P.orderThree (orderThreeProjectedDegreeTwoGenerator F 3) = ![0, 1] := by
  rw [orderThreeProjectedDegreeTwoGenerator, P.orderThree_projection]
  funext i
  fin_cases i <;>
    simp [orderThreeCoinvariantCoordinates, orderThreeCoverCoordinates]

public theorem orderFour_projected_zero (P : ProjectionCoordinates F) :
    P.orderFour (orderFourProjectedDegreeTwoGenerator F 0) = ![2, -3] := by
  rw [orderFourProjectedDegreeTwoGenerator, P.orderFour_projection]
  funext i
  fin_cases i <;>
    simp [orderFourCoinvariantCoordinates, orderFourCoverCoordinates]

public theorem orderFour_projected_three (P : ProjectionCoordinates F) :
    P.orderFour (orderFourProjectedDegreeTwoGenerator F 3) = ![0, 1] := by
  rw [orderFourProjectedDegreeTwoGenerator, P.orderFour_projection]
  funext i
  fin_cases i <;>
    simp [orderFourCoinvariantCoordinates, orderFourCoverCoordinates]

/-- The two Wang-coordinate naturality squares imply the exact finite basis package used by the
rest of Section 7. -/
public theorem basisFiniteData (P : ProjectionCoordinates F) :
    Nonempty (EllipticDegreeTwoHomologyBasisFiniteData F) := by
  let e₃ : IntegralSingularHomology 2 (OrderThreeReducedCentralFiber F) ≃ₗ[ℤ]
      (Fin 2 → ℤ) := P.orderThree.toIntLinearEquiv
  let e₄ : IntegralSingularHomology 2 (OrderFourReducedCentralFiber F) ≃ₗ[ℤ]
      (Fin 2 → ℤ) := P.orderFour.toIntLinearEquiv
  have he₃ : (e₃ : _ → _) = P.orderThree := by
    funext x
    rfl
  have he₄ : (e₄ : _ → _) = P.orderFour := by
    funext x
    rfl
  let b₃ : Module.Basis (Fin 2) ℤ
      (IntegralSingularHomology 2 (OrderThreeReducedCentralFiber F)) :=
    Module.Basis.ofEquivFun e₃
  let b₄ : Module.Basis (Fin 2) ℤ
      (IntegralSingularHomology 2 (OrderFourReducedCentralFiber F)) :=
    Module.Basis.ofEquivFun e₄
  refine ⟨{
    orderThreeBasis := b₃
    orderThreeBasis_zero := ?_
    orderThreeBasis_one := ?_
    orderFourBasis := b₄
    orderFourBasis_zero_double := ?_
    orderFourBasis_one := ?_
  }⟩
  · apply e₃.injective
    rw [map_add, map_nsmul, he₃, P.orderThree_projected_one,
      P.orderThree_projected_three]
    simp only [b₃, Module.Basis.coe_ofEquivFun]
    rw [← he₃, e₃.apply_symm_apply]
    change Pi.single 0 1 = ![1, -2] + 2 • ![0, 1]
    funext i
    fin_cases i <;> norm_num [Pi.single_apply]
  · apply e₃.injective
    rw [he₃, P.orderThree_projected_three]
    simp only [b₃, Module.Basis.coe_ofEquivFun]
    rw [← he₃, e₃.apply_symm_apply]
    change Pi.single 1 1 = ![0, 1]
    funext i
    fin_cases i <;> norm_num [Pi.single_apply]
  · apply e₄.injective
    rw [map_nsmul, map_add, map_nsmul, he₄, P.orderFour_projected_zero,
      P.orderFour_projected_three]
    simp only [b₄, Module.Basis.coe_ofEquivFun]
    rw [← he₄, e₄.apply_symm_apply]
    change 2 • Pi.single 0 1 = ![2, -3] + 3 • ![0, 1]
    funext i
    fin_cases i <;> norm_num [Pi.single_apply]
  · apply e₄.injective
    rw [he₄, P.orderFour_projected_three]
    simp only [b₄, Module.Basis.coe_ofEquivFun]
    rw [← he₄, e₄.apply_symm_apply]
    change Pi.single 1 1 = ![0, 1]
    funext i
    fin_cases i <;> norm_num [Pi.single_apply]

end ProjectionCoordinates

end SphereSixComplex.Topology.EllipticDegreeTwoBasisFromMappingTorusCoordinates

end

end
