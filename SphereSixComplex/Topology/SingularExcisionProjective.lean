module

public import SphereSixComplex.Topology.SingularExcision
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Projective reduction for the small-chain theorem

Integral simplicial chain groups are free abelian and hence projective.  Consequently, for the
nonnegatively graded singular chain complexes used by the excision development, it is enough to
prove that the cover-small inclusion is a quasi-isomorphism: projectivity upgrades it to the
chain-homotopy equivalence packaged by `CoverSmallChainApproximation`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped Simplicial

namespace SphereSixComplex

/-- The homological form of the small-chain theorem: the cover-small inclusion induces an
isomorphism on homology in every degree. -/
public def CoverSmallChainQuasiIsomorphism
    {i : Type} (X : TopCat) (U : i → Set X) : Prop :=
  QuasiIso (coverSmallIntegralSingularChainInclusion X U)

/-- A quasi-isomorphism from cover-small to full singular chains supplies the existing
small-chain approximation interface. -/
public theorem coverSmallChainApproximation_of_quasiIso
    {i : Type} (X : TopCat) (U : i → Set X)
    (h : CoverSmallChainQuasiIsomorphism X U) :
    CoverSmallChainApproximation X U := by
  letI : QuasiIso (coverSmallIntegralSingularChainInclusion X U) := h
  letI projectiveInteger : Projective (AddCommGrpCat.of ℤ) := by
    exact ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.map_projective_iff
      (ModuleCat.of ℤ ℤ)).mpr (by infer_instance)
  letI projectiveSmall (n : ℕ) :
      Projective ((CoverSmallIntegralSingularChainComplex X U).X n) := by
    change Projective
      (∐ fun _ : (coverSmallSingularSubcomplex X U : SSet).obj
          (Opposite.op (SimplexCategory.mk n)) ↦
        AddCommGrpCat.of ℤ)
    infer_instance
  letI projectiveFull (n : ℕ) :
      Projective ((IntegralSingularChainComplexObj X).X n) := by
    change Projective
      (∐ fun _ : (TopCat.toSSet.obj X).obj
          (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ)
    infer_instance
  exact (ChainComplex.quasiIso_iff_of_projective
    (coverSmallIntegralSingularChainInclusion X U)).mp (by infer_instance)

/-- The remaining homological small-chain statement for the concrete disk cover. -/
public def DiskSevenSmallChainQuasiIsomorphism : Prop :=
  CoverSmallChainQuasiIsomorphism (TopCat.disk.{0} 7) diskSevenExcisionCover

/-- For the concrete disk cover, homological excision is enough to recover the stronger
chain-homotopy-equivalence statement used downstream. -/
public theorem diskSevenSmallChainApproximation_of_quasiIso
    (h : DiskSevenSmallChainQuasiIsomorphism) :
    DiskSevenSmallChainApproximation :=
  coverSmallChainApproximation_of_quasiIso
    (TopCat.disk.{0} 7) diskSevenExcisionCover h

end SphereSixComplex
