module

public import SphereSixComplex.Paper.Topology.PaperCuspSpecializationAlgebra
public import SphereSixComplex.Prerequisites.Topology.WangHomologySplitting

/-!
# Homology bases for a circle mapping torus

This module splits the Wang short exact sequence when its invariant term is projective, then
specializes the construction to the cusp monodromy matrices in degrees zero, one, and two.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex

namespace CircleMappingTorusHomologyBases

open LatticeData
open LatticeWangAlgebra
open Topology.PaperCuspSpecializationAlgebra

/-- Fiber coordinates through degree two that identify monodromy with the cusp matrices. -/
public structure CuspMonodromyCoordinates
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) where
  degreeZero : IntegralSingularHomology 0 F ≃+ ℤ
  degreeOne : IntegralSingularHomology 1 F ≃+ Lattice
  degreeTwo : IntegralSingularHomology 2 F ≃+ ExteriorTwoLattice
  degreeZero_monodromy : ∀ x,
    degreeZero (integralSingularHomologyMap 0 phi x) = degreeZero x
  degreeOne_monodromy : ∀ x,
    degreeOne (integralSingularHomologyMap 1 phi x) = M₀ *ᵥ degreeOne x
  degreeTwo_monodromy : ∀ x,
    degreeTwo (integralSingularHomologyMap 2 phi x) =
      mZeroExteriorTwoMatrix *ᵥ degreeTwo x

public def zeroKernelEquivInt : LinearMap.ker (0 : ℤ →ₗ[ℤ] ℤ) ≃ₗ[ℤ] ℤ where
  toFun x := x.1
  invFun x := ⟨x, by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

public def finTwoProdIntLinearEquiv : ((Fin 2 → ℤ) × ℤ) ≃ₗ[ℤ] (Fin 3 → ℤ) where
  toFun x := ![x.1 0, x.1 1, x.2]
  invFun x := (![x 0, x 1], x 2)
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' n x := by
    funext i
    fin_cases i <;> rfl
  left_inv x := by
    rcases x with ⟨x, y⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

public def finFourProdFinTwoLinearEquiv :
    ((Fin 4 → ℤ) × (Fin 2 → ℤ)) ≃ₗ[ℤ] (Fin 6 → ℤ) where
  toFun x := ![x.1 0, x.1 1, x.1 2, x.1 3, x.2 0, x.2 1]
  invFun x := (![x 0, x 1, x 2, x 3], ![x 4, x 5])
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' n x := by
    funext i
    fin_cases i <;> rfl
  left_inv x := by
    rcases x with ⟨x, y⟩
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

namespace CuspMonodromyCoordinates

variable {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}

public theorem degreeZeroDifference_conjugacy (B : CuspMonodromyCoordinates phi) :
    B.degreeZero.toIntLinearEquiv.toLinearMap.comp
        (circleMonodromyDifference phi 0).toIntLinearMap =
      (0 : ℤ →ₗ[ℤ] ℤ).comp B.degreeZero.toIntLinearEquiv.toLinearMap := by
  simpa using circleDifference_conjugacy phi 0 B.degreeZero.toIntLinearEquiv LinearMap.id
    (fun x ↦ by simpa using B.degreeZero_monodromy x)

public theorem degreeOneDifference_conjugacy (B : CuspMonodromyCoordinates phi) :
    B.degreeOne.toIntLinearEquiv.toLinearMap.comp
        (circleMonodromyDifference phi 1).toIntLinearMap =
      mZeroDifference.comp B.degreeOne.toIntLinearEquiv.toLinearMap := by
  exact circleDifference_conjugacy phi 1 B.degreeOne.toIntLinearEquiv M₀.mulVecLin
    B.degreeOne_monodromy

public theorem degreeTwoDifference_conjugacy (B : CuspMonodromyCoordinates phi) :
    B.degreeTwo.toIntLinearEquiv.toLinearMap.comp
        (circleMonodromyDifference phi 2).toIntLinearMap =
      mZeroExteriorTwoDifference.comp B.degreeTwo.toIntLinearEquiv.toLinearMap := by
  exact circleDifference_conjugacy phi 2 B.degreeTwo.toIntLinearEquiv
    mZeroExteriorTwoMatrix.mulVecLin B.degreeTwo_monodromy

/-- The first homology of the cusp circle mapping torus is free of rank three. -/
public noncomputable def circleMappingTorusHOneLinearEquiv
    (B : CuspMonodromyCoordinates phi) :
    IntegralSingularHomology 1 (CircleMappingTorus phi) ≃ₗ[ℤ] (Fin 3 → ℤ) := by
  let P := circleMappingTorusHOnePresentation phi
  let coinvariants :=
    (coinvariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
      (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
      B.degreeOneDifference_conjugacy).trans mZeroCoinvariantsEquivIntSquared
  let invariants :=
    (invariantsEquivOfConjugacy B.degreeZero.toIntLinearEquiv
      (circleMonodromyDifference phi 0).toIntLinearMap 0
      B.degreeZeroDifference_conjugacy).trans zeroKernelEquivInt
  exact (P.linearEquivOfCoordinates coinvariants invariants).trans
    finTwoProdIntLinearEquiv

/-- The second homology of the cusp circle mapping torus is free of rank six. -/
public noncomputable def circleMappingTorusHTwoLinearEquiv
    (B : CuspMonodromyCoordinates phi) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) ≃ₗ[ℤ] (Fin 6 → ℤ) := by
  let P := circleMappingTorusHTwoPresentation phi
  let coinvariants :=
    (coinvariantsEquivOfConjugacy B.degreeTwo.toIntLinearEquiv
      (circleMonodromyDifference phi 2).toIntLinearMap mZeroExteriorTwoDifference
      B.degreeTwoDifference_conjugacy).trans mZeroExteriorTwoCoinvariantsEquivIntFourth
  let invariants :=
    (invariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
      (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
      B.degreeOneDifference_conjugacy).trans mZeroInvariantsEquivIntSquared
  exact (P.linearEquivOfCoordinates coinvariants invariants).trans
    finFourProdFinTwoLinearEquiv

/-- Additive coordinates on first homology, for direct use with singular homology APIs. -/
public noncomputable def circleMappingTorusHOneAddEquiv
    (B : CuspMonodromyCoordinates phi) :
    IntegralSingularHomology 1 (CircleMappingTorus phi) ≃+ (Fin 3 → ℤ) :=
  B.circleMappingTorusHOneLinearEquiv.toAddEquiv

/-- Additive coordinates on second homology, for direct use with singular homology APIs. -/
public noncomputable def circleMappingTorusHTwoAddEquiv
    (B : CuspMonodromyCoordinates phi) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) ≃+ (Fin 6 → ℤ) :=
  B.circleMappingTorusHTwoLinearEquiv.toAddEquiv

end CuspMonodromyCoordinates

end CircleMappingTorusHomologyBases

end SphereSixComplex
