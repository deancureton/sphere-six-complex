module

public import SphereSixComplex.Topology.SectionSevenLerayRealization
public import SphereSixComplex.Topology.SmoothRecognition
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

/-- Mathlib's categorical six-sphere is literally the boundary of its seven-disk. -/
public theorem topCatSphereSix_eq_diskBoundarySeven :
    TopCat.sphere 6 = TopCat.diskBoundary 7 :=
  rfl

/-- The concrete inclusion of the project's six-sphere into mathlib's seven-disk. -/
public noncomputable def sixSphereDiskBoundaryInclusion :
    TopCat.of SixSphere ⟶ TopCat.disk 7 :=
  TopCat.ofHom
      ⟨sixSphereHomeomorphTopCatSphereSix,
        sixSphereHomeomorphTopCatSphereSix.continuous⟩ ≫
    TopCat.diskBoundaryInclusion 7

/-- The categorical six-sphere inherits path-connectedness from the project's concrete sphere. -/
public theorem topCatSphereSix_pathConnectedSpace :
    PathConnectedSpace (TopCat.sphere 6 : Type) := by
  let _ : PathConnectedSpace SixSphere := sixSphere_pathConnectedSpace
  exact pathConnectedSpace_of_homeomorph sixSphereHomeomorphTopCatSphereSix

/-- The unconditional degree-zero integral singular homology calculation for the standard
six-sphere. -/
public noncomputable def sixSphere_integralSingularHomology_zero_equiv_integer :
    IntegralSingularHomology 0 SixSphere ≃+ ℤ := by
  let _ : PathConnectedSpace SixSphere := sixSphere_pathConnectedSpace
  exact (asIso ((TopCat.of SixSphere).singularHomology₀ε (AddCommGrpCat.of ℤ)))
    |>.addCommGroupIsoToAddEquiv

/-- The degree-zero component of the standard sphere's Section 7 realization is now concrete. -/
public theorem sixSphere_sectionSevenHomologyRealization_zero :
    Nonempty (IntegralSingularHomology 0 SixSphere ≃+ SectionSevenComputedHomology 0) :=
  ⟨sixSphere_integralSingularHomology_zero_equiv_integer.trans
    sectionSevenComputedHomologyZeroEquivInteger.symm⟩

/-- Mathlib's seven-disk is contractible, by convexity of the closed Euclidean ball. -/
public theorem topCatDiskSeven_contractibleSpace :
    ContractibleSpace (TopCat.disk 7 : Type) := by
  change ContractibleSpace (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 7)) 1))
  let _ : ContractibleSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 7)) 1) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  exact Homeomorph.ulift.contractibleSpace

/-- Degree-zero integral singular homology of the seven-disk. -/
public noncomputable def topCatDiskSeven_integralSingularHomology_zero_equiv_integer :
    IntegralSingularHomology 0 (TopCat.disk 7 : Type) ≃+ ℤ := by
  let _ : ContractibleSpace (TopCat.disk 7 : Type) := topCatDiskSeven_contractibleSpace
  exact (asIso ((TopCat.disk 7).singularHomology₀ε (AddCommGrpCat.of ℤ)))
    |>.addCommGroupIsoToAddEquiv

/-- All positive-degree integral singular homology objects of the seven-disk vanish. -/
public theorem topCatDiskSeven_integralSingularHomology_isZero
    (k : ℕ) (hk : k ≠ 0) :
    IsZero (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.disk 7)) := by
  let _ : ContractibleSpace (TopCat.disk 7 : Type) := topCatDiskSeven_contractibleSpace
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit (TopCat.disk 7 : Type)
  have hunit := AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    AddCommGrpCat k (AddCommGrpCat.of ℤ) (TopCat.of Unit) hk
  let _ : Subsingleton (IntegralSingularHomology k Unit) :=
    AddCommGrpCat.subsingleton_of_isZero hunit
  let he := integralSingularHomologyEquivOfHomotopyEquiv k e
  let _ : Subsingleton (IntegralSingularHomology k (TopCat.disk 7 : Type)) :=
    ⟨fun x y ↦ he.injective (Subsingleton.elim _ _)⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

end SphereSixComplex
