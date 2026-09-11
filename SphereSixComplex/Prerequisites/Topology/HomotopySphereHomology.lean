module

public import SphereSixComplex.Prerequisites.Topology.SmoothRecognition
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Homology transport for marked homotopy six-spheres

A marking is an actual homotopy equivalence with the standard six-sphere.  This file packages the
resulting singular-homology isomorphism for arbitrary coefficients in `AddCommGrpCat`, so the
mod-two middle-homology input in the Kervaire argument reduces exactly to the corresponding
calculation for the standard sphere.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits ContinuousMap

namespace SphereSixComplex

/-- Singular homology with arbitrary abelian-group coefficients is invariant under a specified
homotopy equivalence. -/
public noncomputable def singularHomologyIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (R : AddCommGrpCat) (k : ℕ) (e : X ≃ₕ Y) :
    ((singularHomologyFunctor AddCommGrpCat k).obj R).obj (TopCat.of X) ≅
      ((singularHomologyFunctor AddCommGrpCat k).obj R).obj (TopCat.of Y) := by
  let F := (singularHomologyFunctor AddCommGrpCat k).obj R
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  exact CategoryTheory.Iso.mk (F.map f) (F.map g) (by
    rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      e.left_inv.some R k) (by
    rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      e.right_inv.some R k)




end SphereSixComplex
