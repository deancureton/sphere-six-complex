module

public import SphereSixComplex.Prerequisites.Topology.SmoothRecognition
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Topology.Category.TopCat.Sphere

/-!
# Degree-zero integral homology of the six-sphere

Path connectedness makes the canonical degree-zero augmentation an isomorphism with ℤ.
The project's sphere is also identified with Mathlib's categorical sphere.
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
