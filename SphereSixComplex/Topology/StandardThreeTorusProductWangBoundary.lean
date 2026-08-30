module

public import SphereSixComplex.Topology.FiniteCyclicMappingTorusWangNaturality
public import SphereSixComplex.Topology.FiniteCyclicThreeTorusWangNaturality

/-!
# The oriented product Wang boundary for the standard three-torus

The canonical coordinates on `H₂(S¹ × T³; ℤ)` split into the three base-circle cross
fibre-circle classes and the three fibre two-torus classes.  This file constructs the resulting
oriented product Wang presentation directly from those coordinates.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.StandardThreeTorusProductWangBoundary

open FiniteCyclicMappingTorusWangNaturality
open FiniteCyclicThreeTorusWangNaturality
open PaperAffineCyclicReducedFiberMappingTorus
open StandardTorusHomology

/-- Assemble the base-cross and fibre coordinates in the standard pair ordering. -/
public def joinCoordinates (a b : ThreeLattice) : SixLattice :=
  ![a 0, a 1, a 2, b 0, b 1, b 2]

@[simp]
public theorem baseCrossDegreeOne_joinCoordinates (a b : ThreeLattice) :
    baseCrossDegreeOne (joinCoordinates a b) = a := by
  funext i
  fin_cases i <;> rfl

@[simp]
public theorem fibreDegreeTwo_joinCoordinates (a b : ThreeLattice) :
    fibreDegreeTwo (joinCoordinates a b) = b := by
  funext i
  fin_cases i <;> rfl

public theorem joinCoordinates_baseCross_fibre (x : SixLattice) :
    joinCoordinates (baseCrossDegreeOne x) (fibreDegreeTwo x) = x := by
  funext i
  fin_cases i <;> rfl

private theorem gammaSplit_symm_comp_fiberInclusion :
    (standardFourTorusGammaSplit.symm : C(UnitAddCircle × StdTorus 3, StdTorus 4)).comp
        (circleProductFiberInclusion (X := StdTorus 3)) =
      standardThreeTorusTailInclusion := by
  ext x i
  fin_cases i <;> rfl

/-- In product coordinates, fibre inclusion occupies exactly the last three coordinates. -/
public theorem productHomologyTwo_fiberInclusion
    (x : IntegralSingularHomology 2 (StdTorus 3)) :
    productHomologyTwo
        (integralSingularHomologyMap 2
          (circleProductFiberInclusion (X := StdTorus 3)) x) =
      joinCoordinates 0 (standardThreeTorusHomologyTwo x) := by
  rw [productHomologyTwo, standardCircleProdThreeTorusHomologyTwo_apply]
  rw [integralSingularHomologyMap_comp_wang, gammaSplit_symm_comp_fiberInclusion]
  rw [standardThreeTorusTailInclusion_homologyTwo_coordinates]
  rfl

/-- The positively oriented product Wang boundary: retain the three base-cross coordinates and
read them as the canonical degree-one class of the fibre. -/
public def orientedProductBoundary :
    IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3) →+
      IntegralSingularHomology 1 (StdTorus 3) :=
  standardThreeTorusHomologyOne.symm.toAddMonoidHom.comp
    (baseCrossDegreeOne.toAddMonoidHom.comp productHomologyTwo.toAddMonoidHom)

@[simp]
public theorem standardThreeTorusHomologyOne_orientedProductBoundary
    (z : IntegralSingularHomology 2 (UnitAddCircle × StdTorus 3)) :
    standardThreeTorusHomologyOne (orientedProductBoundary z) =
      baseCrossDegreeOne (productHomologyTwo z) := by
  exact standardThreeTorusHomologyOne.apply_symm_apply _

public theorem orientedProductBoundary_surjective :
    Function.Surjective orientedProductBoundary := by
  intro x
  refine ⟨productHomologyTwo.symm
    (joinCoordinates (standardThreeTorusHomologyOne x) 0), ?_⟩
  apply standardThreeTorusHomologyOne.injective
  rw [standardThreeTorusHomologyOne_orientedProductBoundary]
  simp

public theorem circleProductFiberInclusion_homologyTwo_injective :
    Function.Injective
      (integralSingularHomologyMap 2
        (circleProductFiberInclusion (X := StdTorus 3))) := by
  intro x y hxy
  apply standardThreeTorusHomologyTwo.injective
  have h := congrArg productHomologyTwo hxy
  rw [productHomologyTwo_fiberInclusion, productHomologyTwo_fiberInclusion] at h
  simpa using congrArg fibreDegreeTwo h

public theorem exact_fiberInclusion_orientedProductBoundary :
    Function.Exact
      (integralSingularHomologyMap 2
        (circleProductFiberInclusion (X := StdTorus 3)))
      orientedProductBoundary := by
  intro z
  constructor
  · intro hz
    have hbase : baseCrossDegreeOne (productHomologyTwo z) = 0 := by
      rw [← standardThreeTorusHomologyOne_orientedProductBoundary, hz, map_zero]
    let x := standardThreeTorusHomologyTwo.symm
      (fibreDegreeTwo (productHomologyTwo z))
    refine ⟨x, ?_⟩
    apply productHomologyTwo.injective
    calc
      productHomologyTwo
          (integralSingularHomologyMap 2
            (circleProductFiberInclusion (X := StdTorus 3)) x) =
          joinCoordinates 0 (standardThreeTorusHomologyTwo x) :=
        productHomologyTwo_fiberInclusion x
      _ = joinCoordinates 0 (fibreDegreeTwo (productHomologyTwo z)) := by
        rw [show standardThreeTorusHomologyTwo x =
          fibreDegreeTwo (productHomologyTwo z) from
            standardThreeTorusHomologyTwo.apply_symm_apply _]
      _ = joinCoordinates (baseCrossDegreeOne (productHomologyTwo z))
          (fibreDegreeTwo (productHomologyTwo z)) := by rw [hbase]
      _ = productHomologyTwo z := joinCoordinates_baseCross_fibre _
  · rintro ⟨x, rfl⟩
    apply standardThreeTorusHomologyOne.injective
    rw [standardThreeTorusHomologyOne_orientedProductBoundary,
      productHomologyTwo_fiberInclusion]
    simp

/-- The explicit oriented product presentation in total degree two. -/
public noncomputable def orientedProductWangPresentation :
    CircleProductWangPresentation (StdTorus 3) 1 where
  boundary := orientedProductBoundary
  inclusion_injective := circleProductFiberInclusion_homologyTwo_injective
  exact_inclusion_boundary := exact_fiberInclusion_orientedProductBoundary
  boundary_surjective := orientedProductBoundary_surjective

end SphereSixComplex.Topology.StandardThreeTorusProductWangBoundary

end

end
