module

public import SphereSixComplex.Prerequisites.Topology.Sphere.HomologySphere
public import SphereSixComplex.Prerequisites.Topology.Sphere.SimplyConnected
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Smooth recognition of the six-sphere

This file packages the inputs to six-dimensional smooth sphere recognition.
`Recognition` combines h-cobordism with smooth six-sphere classification for the specified atlas.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- Integral singular homology is invariant under a homotopy equivalence. -/
public noncomputable def integralSingularHomologyEquivOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (k : ℕ) (e : X ≃ₕ Y) :
    IntegralSingularHomology k X ≃+ IntegralSingularHomology k Y := by
  let F := (singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  let i : F.obj (TopCat.of X) ≅ F.obj (TopCat.of Y) :=
    CategoryTheory.Iso.mk (F.map f) (F.map g) (by
      rw [← F.map_comp, ← F.map_id]
      exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        e.left_inv.some (AddCommGrpCat.of ℤ) k) (by
      rw [← F.map_comp, ← F.map_id]
      exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        e.right_inv.some (AddCommGrpCat.of ℤ) k)
  exact i.addCommGroupIsoToAddEquiv

/-- A compact connected smooth manifold modelled on real six-space. -/
public structure CompactConnectedSmoothSixManifold (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop where
  /-- Smoothness of the given atlas. -/
  isManifold : IsManifold 𝓘(ℝ, RealModel) ∞ X
  /-- Compactness of the underlying space. -/
  compact : CompactSpace X
  /-- Connectedness of the underlying space. -/
  connected : ConnectedSpace X

/-- A compact connected smooth six-manifold with the integral singular homology of `S⁶`. -/
public structure SmoothIntegralHomologySixSphere (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop extends CompactConnectedSmoothSixManifold X where
  /-- Degreewise integral singular homology agrees with the standard six-sphere. -/
  integralHomology : HasIntegralHomologyOfSixSphere X

/-- The recognition input consisting of a simply connected smooth integral homology six-sphere. -/
public structure SmoothSimplyConnectedIntegralHomologySixSphere (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop extends SmoothIntegralHomologySixSphere X where
  /-- The underlying space is simply connected. -/
  simplyConnected : SimplyConnectedSpace X

end SphereSixComplex
