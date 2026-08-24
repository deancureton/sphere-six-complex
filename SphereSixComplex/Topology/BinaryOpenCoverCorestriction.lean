/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.BinaryOpenCoverChains
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Singular chains of an open subspace and its image subcomplex

The inclusion of an open subspace is injective, so its singular simplicial set is isomorphic to
the range subcomplex of the ambient singular set. Applying integral simplicial chains and then
homology preserves this isomorphism.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace

namespace SphereSixComplex.BinaryOpenCover

/-- Corestricting the singular map of an open inclusion to its range is an isomorphism. -/
public noncomputable instance singularOpenCorestriction_isIso {X : TopCat} (U : Opens X) :
    IsIso (singularOpenCorestriction U) := by
  letI : Mono (Opens.inclusion' U) :=
    (TopCat.mono_iff_injective (Opens.inclusion' U)).2 Subtype.val_injective
  letI : Mono (TopCat.toSSet.map (Opens.inclusion' U)) := by infer_instance
  change IsIso
    (SSet.Subcomplex.toRange (TopCat.toSSet.map (Opens.inclusion' U)))
  infer_instance

/-- The integral chain map induced by corestriction to the open-image subcomplex. -/
public noncomputable def singularOpenCorestrictionChainMap {X : TopCat} (U : Opens X) :
    integralSimplicialChains.obj (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)) ⟶
      integralSimplicialChains.obj (singularOpenSubcomplex U) :=
  integralSimplicialChains.map (singularOpenCorestriction U)

/-- Integral chains preserve the open-corestriction isomorphism. -/
public noncomputable instance singularOpenCorestrictionChainMap_isIso {X : TopCat}
    (U : Opens X) : IsIso (singularOpenCorestrictionChainMap U) := by
  dsimp [singularOpenCorestrictionChainMap]
  infer_instance

/-- The homology map induced by corestriction to the open-image subcomplex. -/
public noncomputable def singularOpenCorestrictionHomologyMap {X : TopCat}
    (U : Opens X) (n : ℕ) :=
  HomologicalComplex.homologyMap (singularOpenCorestrictionChainMap U) n

/-- In every degree, open corestriction induces an isomorphism on integral homology. -/
public noncomputable instance singularOpenCorestrictionHomologyMap_isIso {X : TopCat}
    (U : Opens X) (n : ℕ) : IsIso (singularOpenCorestrictionHomologyMap U n) := by
  dsimp [singularOpenCorestrictionHomologyMap]
  change IsIso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat _ n).map
      (singularOpenCorestrictionChainMap U))
  infer_instance

end SphereSixComplex.BinaryOpenCover
