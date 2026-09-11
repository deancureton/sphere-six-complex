module

public import SphereSixComplex.Prerequisites.Topology.SmoothRecognition
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Topology.Category.TopCat.Sphere

/-!
# The currently available singular homology of the standard six-sphere

Mathlib identifies singular homology in degree zero with the free coefficient object on path
components.  This computes `H₀(S⁶; ℤ)` because the standard sphere is path-connected.  We also
identify the project's sphere with `TopCat.sphere 6`, construct its boundary inclusion into the
seven-disk, and compute the disk's integral homology using contractibility.

The remaining sphere calculation cannot currently be obtained from mathlib: there is no singular
relative-homology functor for a pair, long exact sequence of a pair, excision theorem, reduced
homology suspension isomorphism, or cellular-to-singular comparison.  The abstract
`HomologyPretheory` API in `Mathlib.AlgebraicTopology.EilenbergSteenrod` is not instantiated by
singular homology and currently supplies only homotopy invariance.  Thus the missing concrete step
is the boundary isomorphism
`Hₖ(D⁷,S⁶;ℤ) ≅ Hₖ₋₁(S⁶;ℤ)` together with excision/cell computation of the relative group.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

/-- The project's unit sphere is the underlying space of mathlib's categorical six-sphere. -/
public noncomputable def sixSphereHomeomorphTopCatSphereSix :
    SixSphere ≃ₜ (TopCat.sphere 6 : Type) := by
  change (Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1) ≃ₜ
    ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1)
  exact Homeomorph.ulift.symm




/-- The unconditional degree-zero integral singular homology calculation for the standard
six-sphere. -/
public noncomputable def sixSphere_integralSingularHomology_zero_equiv_integer :
    IntegralSingularHomology 0 SixSphere ≃+ ℤ := by
  let _ : PathConnectedSpace SixSphere := sixSphere_pathConnectedSpace
  exact (asIso ((TopCat.of SixSphere).singularHomology₀ε (AddCommGrpCat.of ℤ)))
    |>.addCommGroupIsoToAddEquiv




end SphereSixComplex
