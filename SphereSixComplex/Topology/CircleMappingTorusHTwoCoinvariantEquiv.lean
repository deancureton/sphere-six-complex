module

public import SphereSixComplex.Topology.CircleMappingTorusHomologyBases

/-!
# Second homology of a mapping torus with no degree-one invariants

If the degree-one monodromy has no invariants, the upper map in the Wang sequence identifies
second homology of the mapping torus with the degree-two monodromy coinvariants.  This is the
source-independent algebraic step used for the two elliptic clutching maps.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

namespace WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]

/-- If the invariant end of a Wang presentation vanishes, its total term is canonically
equivalent to the upper coinvariants. -/
public noncomputable def coinvariantsLinearEquivTotalOfSubsingletonInvariants
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    [Subsingleton P.Invariants] : P.Coinvariants ≃ₗ[ℤ] Total := by
  apply LinearEquiv.ofBijective P.coinvariantsToTotal
  refine ⟨P.coinvariantsToTotal_injective, ?_⟩
  intro x
  apply (P.exact_coinvariantsToTotal_totalToInvariants x).mp
  exact Subsingleton.elim _ 0

@[simp]
public theorem coinvariantsLinearEquivTotalOfSubsingletonInvariants_apply
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    [Subsingleton P.Invariants] (x : P.Coinvariants) :
    P.coinvariantsLinearEquivTotalOfSubsingletonInvariants x = P.coinvariantsToTotal x :=
  rfl

@[simp]
public theorem coinvariantsLinearEquivTotalOfSubsingletonInvariants_symm_inclusion
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    [Subsingleton P.Invariants] (x : High) :
    P.coinvariantsLinearEquivTotalOfSubsingletonInvariants.symm (P.inclusion x) =
      Submodule.Quotient.mk x := by
  apply P.coinvariantsLinearEquivTotalOfSubsingletonInvariants.injective
  rw [P.coinvariantsLinearEquivTotalOfSubsingletonInvariants.apply_symm_apply]
  rfl

end WangHomologyPresentation

open CircleMappingTorusHomologyBases

variable {F C Q : Type} [TopologicalSpace F]
  [AddCommGroup C] [AddCommGroup Q]

/-- The degree-two Wang coinvariants give all of mapping-torus degree-two homology when the
degree-one monodromy difference is injective. -/
public noncomputable def circleMappingTorusHTwoCoinvariantsLinearEquiv
    (phi : F ≃ₜ F) (hinjective : Function.Injective
      (circleMonodromyDifference phi 1).toIntLinearMap) :
    (circleMappingTorusHTwoPresentation phi).Coinvariants ≃ₗ[ℤ]
      IntegralSingularHomology 2 (CircleMappingTorus phi) := by
  let _ : Subsingleton (circleMappingTorusHTwoPresentation phi).Invariants :=
    ⟨fun x y ↦ Subtype.ext (hinjective (by
      exact (LinearMap.mem_ker.mp x.2).trans (LinearMap.mem_ker.mp y.2).symm))⟩
  exact WangHomologyPresentation.coinvariantsLinearEquivTotalOfSubsingletonInvariants
    (circleMappingTorusHTwoPresentation phi)

@[simp]
public theorem circleMappingTorusHTwoCoinvariantsLinearEquiv_mk
    (phi : F ≃ₜ F) (hinjective : Function.Injective
      (circleMonodromyDifference phi 1).toIntLinearMap)
    (x : IntegralSingularHomology 2 F) :
    circleMappingTorusHTwoCoinvariantsLinearEquiv phi hinjective
        (Submodule.Quotient.mk x) =
      integralSingularHomologyMap 2
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) x := by
  let _ : Subsingleton (circleMappingTorusHTwoPresentation phi).Invariants :=
    ⟨fun y z ↦ Subtype.ext (hinjective (by
      exact (LinearMap.mem_ker.mp y.2).trans (LinearMap.mem_ker.mp z.2).symm))⟩
  change (WangHomologyPresentation.coinvariantsLinearEquivTotalOfSubsingletonInvariants
      (circleMappingTorusHTwoPresentation phi)) (Submodule.Quotient.mk x) = _
  rfl

/-- Put coordinates on mapping-torus second homology from coordinates on the fibre coinvariants,
provided the degree-one monodromy has no invariants. -/
public noncomputable def circleMappingTorusHTwoLinearEquivOfCoinvariantCoordinates
    (phi : F ≃ₜ F)
    (hinjectiveOne : Function.Injective
      (circleMonodromyDifference phi 1).toIntLinearMap)
    (fiberCoordinates : IntegralSingularHomology 2 F ≃ₗ[ℤ] C)
    (difference : C →ₗ[ℤ] C)
    (difference_conjugacy : fiberCoordinates.toLinearMap.comp
        (circleMonodromyDifference phi 2).toIntLinearMap =
      difference.comp fiberCoordinates.toLinearMap)
    (coinvariantCoordinates :
      (C ⧸ LinearMap.range difference) ≃ₗ[ℤ] Q) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) ≃ₗ[ℤ] Q :=
  (circleMappingTorusHTwoCoinvariantsLinearEquiv phi hinjectiveOne).symm.trans
    ((coinvariantsEquivOfConjugacy fiberCoordinates
      (circleMonodromyDifference phi 2).toIntLinearMap difference
      difference_conjugacy).trans coinvariantCoordinates)

@[simp]
public theorem circleMappingTorusHTwoLinearEquivOfCoinvariantCoordinates_fiberInclusion
    (phi : F ≃ₜ F)
    (hinjectiveOne : Function.Injective
      (circleMonodromyDifference phi 1).toIntLinearMap)
    (fiberCoordinates : IntegralSingularHomology 2 F ≃ₗ[ℤ] C)
    (difference : C →ₗ[ℤ] C)
    (difference_conjugacy : fiberCoordinates.toLinearMap.comp
        (circleMonodromyDifference phi 2).toIntLinearMap =
      difference.comp fiberCoordinates.toLinearMap)
    (coinvariantCoordinates :
      (C ⧸ LinearMap.range difference) ≃ₗ[ℤ] Q)
    (x : IntegralSingularHomology 2 F) :
    circleMappingTorusHTwoLinearEquivOfCoinvariantCoordinates phi hinjectiveOne
        fiberCoordinates difference difference_conjugacy coinvariantCoordinates
        (integralSingularHomologyMap 2
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) x) =
      coinvariantCoordinates (Submodule.Quotient.mk (fiberCoordinates x)) := by
  change coinvariantCoordinates
      (coinvariantsEquivOfConjugacy fiberCoordinates
        (circleMonodromyDifference phi 2).toIntLinearMap difference
        difference_conjugacy
        ((circleMappingTorusHTwoCoinvariantsLinearEquiv phi hinjectiveOne).symm
          (integralSingularHomologyMap 2
            (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) x))) = _
  rw [← circleMappingTorusHTwoCoinvariantsLinearEquiv_mk phi hinjectiveOne x,
    LinearEquiv.symm_apply_apply]
  rfl

end SphereSixComplex

end

end
