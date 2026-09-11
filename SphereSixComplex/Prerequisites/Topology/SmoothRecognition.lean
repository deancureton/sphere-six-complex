module

public import SphereSixComplex.Prerequisites.Topology.HomologySphere
public import SphereSixComplex.Prerequisites.Topology.SphereSimplyConnected
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Geometry.Manifold.PoincareConjecture

/-!
# Smooth recognition of the six-sphere

This file packages the inputs to six-dimensional smooth sphere recognition.  Mathlib states the
generalized and smooth Poincaré conjectures, but does not yet prove the dimension-six case, nor the
Whitehead--Hurewicz step from simply connected integral homology spheres to homotopy spheres.
Accordingly, those two implications are exposed as exact obligations rather than postulated.
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

/-- A compact connected smooth six-manifold homotopy equivalent to the standard six-sphere. -/
public structure SmoothHomotopySixSphere (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop extends CompactConnectedSmoothSixManifold X where
  /-- A homotopy equivalence to the standard six-sphere. -/
  homotopyEquiv : Nonempty (X ≃ₕ SixSphere)

/-- Smooth diffeomorphism to the standard six-sphere, using the fixed real six-dimensional model. -/
public abbrev SmoothSixSphere.IsDiffeomorphic (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop :=
  Nonempty (Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X SixSphere ∞)

/-- The missing Whitehead--Hurewicz recognition step for a particular smooth six-manifold. -/
public def HomologyToHomotopySixSphereObligation (X : Type) [TopologicalSpace X]
    [ChartedSpace RealModel X] : Prop :=
  SmoothSimplyConnectedIntegralHomologySixSphere X → Nonempty (X ≃ₕ SixSphere)
















end SphereSixComplex
