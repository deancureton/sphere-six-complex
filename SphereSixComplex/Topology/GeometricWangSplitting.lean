module

public import SphereSixComplex.Topology.CircleMappingTorusHomologyBases

/-!
# Geometric splittings of the Wang sequence

The abstract Wang calculation only determines the homology of a mapping torus as an extension.
For maps out of the mapping torus one must fix the geometric suspension classes, rather than use
an arbitrary projective lifting.  This file constructs the resulting coordinates from a supplied
right inverse to the Wang boundary map.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex

namespace WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]

/-- A specified geometric lift of the invariant classes in a Wang presentation. -/
public structure GeometricSection
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low) where
  lift : P.Invariants →ₗ[ℤ] Total
  rightInverse : P.totalToInvariants.comp lift = LinearMap.id

namespace GeometricSection

/-- Choose a section of the Wang boundary when its invariant term is projective. -/
public noncomputable def ofProjective
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    [Module.Projective ℤ P.Invariants] : P.GeometricSection := by
  let lifting := Module.projective_lifting_property P.totalToInvariants LinearMap.id
    P.totalToInvariants_surjective
  exact
    { lift := Classical.choose lifting
      rightInverse := Classical.choose_spec lifting }

end GeometricSection

/-- Split a Wang presentation using a specified geometric section. -/
public noncomputable def totalLinearEquivCoinvariantsProdInvariantsOfSection
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) :
    Total ≃ₗ[ℤ] P.Coinvariants × P.Invariants := by
  let i := P.coinvariantsToTotal
  let p := P.totalToInvariants
  let s := S.lift
  let residual : Total →ₗ[ℤ] Total := LinearMap.id - s.comp p
  have hresidual (x : Total) : residual x ∈ LinearMap.range i := by
    apply (P.exact_coinvariantsToTotal_totalToInvariants (residual x)).mp
    have hsx := DFunLike.congr_fun S.rightInverse (p x)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hsx
    change p (x - s (p x)) = 0
    rw [map_sub, hsx, sub_self]
  let residualRange : Total →ₗ[ℤ] LinearMap.range i :=
    residual.codRestrict (LinearMap.range i) hresidual
  let iEquivRange : P.Coinvariants ≃ₗ[ℤ] LinearMap.range i :=
    LinearEquiv.ofInjective i P.coinvariantsToTotal_injective
  let r : Total →ₗ[ℤ] P.Coinvariants := iEquivRange.symm.toLinearMap.comp residualRange
  let forward : Total →ₗ[ℤ] P.Coinvariants × P.Invariants := r.prod p
  let inverse : P.Coinvariants × P.Invariants →ₗ[ℤ] Total := LinearMap.coprod i s
  refine LinearEquiv.ofLinearMap forward inverse ?_ ?_
  · apply LinearMap.ext
    rintro ⟨y, z⟩
    have hpi (y : P.Coinvariants) : p (i y) = 0 :=
      P.exact_coinvariantsToTotal_totalToInvariants.apply_apply_eq_zero y
    have hps (y : P.Invariants) : p (s y) = y := by
      have hsy := DFunLike.congr_fun S.rightInverse y
      simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] using hsy
    have hr : r (i y + s z) = y := by
      apply iEquivRange.injective
      apply Subtype.ext
      change i (r (i y + s z)) = i y
      have hir : i (r (i y + s z)) = residual (i y + s z) := by
        change i (iEquivRange.symm (residualRange (i y + s z))) = residual (i y + s z)
        exact congrArg Subtype.val
          (iEquivRange.apply_symm_apply (residualRange (i y + s z)))
      rw [hir]
      change i y + s z - s (p (i y + s z)) = i y
      rw [map_add, hpi, hps, map_add, map_zero, zero_add]
      abel
    apply Prod.ext
    · exact hr
    · change p (i y + s z) = z
      rw [map_add, hpi, hps, zero_add]
  · apply LinearMap.ext
    intro x
    have hi : i (r x) = residual x := by
      change i (iEquivRange.symm (residualRange x)) = residual x
      exact congrArg Subtype.val (iEquivRange.apply_symm_apply (residualRange x))
    simp only [LinearMap.comp_apply]
    change i (r x) + s (p x) = x
    rw [hi]
    change x - s (p x) + s (p x) = x
    abel

end WangHomologyPresentation

namespace CircleMappingTorusHomologyBases

open LatticeData LatticeWangAlgebra Topology.PaperCuspSpecializationAlgebra

/-- Geometrically chosen suspension sections in degrees one and two. -/
public structure CuspGeometricWangSections
    {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}
    (B : CuspMonodromyCoordinates phi) where
  degreeOne : (circleMappingTorusHOnePresentation phi).GeometricSection
  degreeTwo : (circleMappingTorusHTwoPresentation phi).GeometricSection

namespace CuspGeometricWangSections

variable {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}
    {B : CuspMonodromyCoordinates phi}

/-- First-homology coordinates whose last coordinate is the specified geometric base-circle
class. -/
public noncomputable def circleMappingTorusHOneLinearEquiv
    (S : CuspGeometricWangSections B) :
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
  exact (P.totalLinearEquivCoinvariantsProdInvariantsOfSection S.degreeOne).trans
    ((coinvariants.prodCongr invariants).trans finTwoProdIntLinearEquiv)

/-- Second-homology coordinates whose last two coordinates are the specified invariant
suspension classes. -/
public noncomputable def circleMappingTorusHTwoLinearEquiv
    (S : CuspGeometricWangSections B) :
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
  exact (P.totalLinearEquivCoinvariantsProdInvariantsOfSection S.degreeTwo).trans
    ((coinvariants.prodCongr invariants).trans finFourProdFinTwoLinearEquiv)

public noncomputable def circleMappingTorusHOneAddEquiv
    (S : CuspGeometricWangSections B) :
    IntegralSingularHomology 1 (CircleMappingTorus phi) ≃+ (Fin 3 → ℤ) :=
  S.circleMappingTorusHOneLinearEquiv.toAddEquiv

public noncomputable def circleMappingTorusHTwoAddEquiv
    (S : CuspGeometricWangSections B) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) ≃+ (Fin 6 → ℤ) :=
  S.circleMappingTorusHTwoLinearEquiv.toAddEquiv

end CuspGeometricWangSections

namespace EstablishedCircleMappingTorusGeometricSections

/-- Projectivity of the two invariant lattices supplies sections of the Wang boundary maps. -/
public noncomputable def sections
    {F : Type} [TopologicalSpace F] {phi : F ≃ₜ F}
    (B : CuspMonodromyCoordinates phi) : CuspGeometricWangSections B := by
  let degreeOnePresentation := circleMappingTorusHOnePresentation phi
  let degreeOneInvariants :=
    (invariantsEquivOfConjugacy B.degreeZero.toIntLinearEquiv
      (circleMonodromyDifference phi 0).toIntLinearMap 0
      B.degreeZeroDifference_conjugacy).trans zeroKernelEquivInt
  letI : Module.Projective ℤ degreeOnePresentation.Invariants :=
    Module.Projective.of_equiv' degreeOneInvariants.symm
  let degreeTwoPresentation := circleMappingTorusHTwoPresentation phi
  let degreeTwoInvariants :=
    (invariantsEquivOfConjugacy B.degreeOne.toIntLinearEquiv
      (circleMonodromyDifference phi 1).toIntLinearMap mZeroDifference
      B.degreeOneDifference_conjugacy).trans mZeroInvariantsEquivIntSquared
  letI : Module.Projective ℤ degreeTwoPresentation.Invariants :=
    Module.Projective.of_equiv' degreeTwoInvariants.symm
  exact
    { degreeOne := WangHomologyPresentation.GeometricSection.ofProjective degreeOnePresentation
      degreeTwo := WangHomologyPresentation.GeometricSection.ofProjective degreeTwoPresentation }

end EstablishedCircleMappingTorusGeometricSections

end CircleMappingTorusHomologyBases

end SphereSixComplex
