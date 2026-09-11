module

public import SphereSixComplex.Prerequisites.Topology.StandardSphere
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Homology-sphere recognition data

This file states the remaining topological recognition input precisely. Integral singular homology
is compared degreewise as an additive group, rather than through ranks or Betti numbers.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- Integral singular homology in degree `k`, regarded as an additive commutative group. -/
public abbrev IntegralSingularHomology (k : ℕ) (X : Type) [TopologicalSpace X] : Type :=
  ((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)

/-- Integral singular homology agrees degreewise with that of the standard six-sphere. -/
public def HasIntegralHomologyOfSixSphere (X : Type) [TopologicalSpace X] : Prop :=
  ∀ k : ℕ, Nonempty (IntegralSingularHomology k X ≃+ IntegralSingularHomology k SixSphere)


/-- A homeomorphism induces an additive equivalence on integral singular homology. -/
public noncomputable def integralSingularHomologyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (k : ℕ) (h : X ≃ₜ Y) :
    IntegralSingularHomology k X ≃+ IntegralSingularHomology k Y :=
  (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).mapIso
    (TopCat.isoOfHomeo h)).addCommGroupIsoToAddEquiv


/-- Path-connectedness transports through a homeomorphism. -/
public theorem pathConnectedSpace_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] (h : X ≃ₜ Y) : PathConnectedSpace Y := by
  rw [pathConnectedSpace_iff_univ]
  simpa only [image_univ, h.surjective.range_eq] using isPathConnected_univ.image h.continuous






end SphereSixComplex
