module

public import SphereSixComplex.Topology.OrientedSmoothHomotopySphere
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

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

/-- Vanishing of a singular-homology group transports backward across a homotopy equivalence. -/
public theorem singularHomology_isZero_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (R : AddCommGrpCat) (k : ℕ) (e : X ≃ₕ Y)
    (hY : IsZero (((singularHomologyFunctor AddCommGrpCat k).obj R).obj (TopCat.of Y))) :
    IsZero (((singularHomologyFunctor AddCommGrpCat k).obj R).obj (TopCat.of X)) :=
  hY.of_iso (singularHomologyIsoOfHomotopyEquiv R k e)

/-- For a marked smooth homotopy six-sphere, every coefficientwise homology-vanishing theorem for
the standard sphere immediately transports to its carrier. -/
public theorem OrientedMarkedSmoothHomotopySixSphere.singularHomology_isZero_of_standard
    (S : OrientedMarkedSmoothHomotopySixSphere) (R : AddCommGrpCat) (k : ℕ)
    (hstandard :
      IsZero (((singularHomologyFunctor AddCommGrpCat k).obj R).obj
        (TopCat.of SixSphere))) :
    IsZero (((singularHomologyFunctor AddCommGrpCat k).obj R).obj
      (TopCat.of S.carrier)) :=
  singularHomology_isZero_of_homotopyEquiv R k S.marking hstandard

/-- The exact middle-dimensional mod-two input for the Kervaire argument on all marked homotopy
six-spheres follows from the single standard-sphere calculation. -/
public theorem markedHomotopySixSphere_modTwoHomology_three_isZero_of_standard
    (hstandard :
      IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
        (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of SixSphere)))
    (S : OrientedMarkedSmoothHomotopySixSphere) :
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of S.carrier)) :=
  S.singularHomology_isZero_of_standard (AddCommGrpCat.of (ZMod 2)) 3 hstandard

end SphereSixComplex
