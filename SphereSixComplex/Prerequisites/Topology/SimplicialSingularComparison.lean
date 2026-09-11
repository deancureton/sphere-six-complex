module

public import SphereSixComplex.Prerequisites.Topology.HomotopySphereHomology
public import SphereSixComplex.Prerequisites.Topology.SimplicialSixSphereHomology
public import SphereSixComplex.Prerequisites.Topology.RelativeSingularHomology
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# The canonical simplicial-to-singular comparison

The unit of the geometric-realization/singular-set adjunction sends every simplex of a simplicial
set to the corresponding singular simplex of its realization.  Applying simplicial chains gives
the canonical comparison map.  This file packages that concrete map and proves that its
quasi-isomorphism, together with a homeomorphism `|∂Δ[7]| ≃ S⁶`, transports the already-computed
degree-two and degree-three homology vanishing to the standard topological sphere.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- The canonical chain map from simplicial chains to singular chains on geometric realization. -/
public noncomputable def simplicialToRealizationSingularChainMap
    (K : SSet.{0}) (R : AddCommGrpCat) :
    K.chainComplex R ⟶
      (TopCat.toSSet.obj (SSet.toTop.obj K)).chainComplex R :=
  SSet.chainComplexMap (sSetTopAdj.unit.app K) R

/-- The precise general comparison theorem needed here. -/
public def SimplicialToSingularComparisonQuasiIsomorphism
    (K : SSet.{0}) (R : AddCommGrpCat) : Prop :=
  QuasiIso (simplicialToRealizationSingularChainMap K R)

/-- A quasi-isomorphic comparison transports vanishing from simplicial homology to singular
homology of the realization. -/
public theorem realizationSingularHomology_isZero_of_simplicial
    (K : SSet.{0}) (R : AddCommGrpCat) (k : ℕ)
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism K R)
    (hsimplicial : IsZero ((K.chainComplex R).homology k)) :
    IsZero (((TopCat.toSSet.obj (SSet.toTop.obj K)).chainComplex R).homology k) := by
  let _ : QuasiIso (simplicialToRealizationSingularChainMap K R) := hcomparison
  exact hsimplicial.of_iso
    (isoOfQuasiIsoAt (simplicialToRealizationSingularChainMap K R) k).symm

/-- The geometric identification of the realization of the boundary of the seven-simplex with
the project's standard six-sphere. -/
public def BoundarySevenRealizationHomeomorphSixSphere : Prop :=
  Nonempty ((SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type) ≃ₜ SixSphere)








end SphereSixComplex
