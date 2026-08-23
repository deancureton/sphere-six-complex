module

public import SphereSixComplex.Topology.StandardSphere
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Simple-connectivity reductions for the six-sphere

Mathlib does not yet provide a sphere-specific simple-connectivity theorem.  This file records the
simply connected stereographic chart domains and reduces the global statement exactly to the
remaining loop-nullhomotopy obligation.
-/

@[expose] public section

noncomputable section

open Set

namespace SphereSixComplex

/-- A stereographic chart on the standard six-sphere with its dimension witness packaged. -/
public noncomputable def sixSphereStereographic (v : SixSphere) :
    OpenPartialHomeomorph SixSphere (EuclideanSpace ℝ (Fin 6)) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 7)) = 6 + 1) :=
    ⟨by norm_num [finrank_euclideanSpace_fin]⟩
  exact stereographic' 6 v

@[simp]
public theorem sixSphereStereographic_source (v : SixSphere) :
    (sixSphereStereographic v).source = {v}ᶜ := by
  simp [sixSphereStereographic]

@[simp]
public theorem sixSphereStereographic_target (v : SixSphere) :
    (sixSphereStereographic v).target = Set.univ := by
  simp [sixSphereStereographic]

/-- Every stereographic chart domain of the standard six-sphere is simply connected. -/
public theorem sixSphere_stereographicSource_simplyConnected (v : SixSphere) :
    SimplyConnectedSpace (sixSphereStereographic v).source := by
  let e := (sixSphereStereographic v).toHomeomorphSourceTarget
  rw [e.toHomotopyEquiv.simplyConnectedSpace_iff]
  rw [sixSphereStereographic_target]
  exact (Homeomorph.Set.univ _).toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance

/-- Removing any one point from the standard six-sphere leaves a simply connected space. -/
public theorem sixSphere_compl_singleton_simplyConnected (v : SixSphere) :
    SimplyConnectedSpace ({v}ᶜ : Set SixSphere) := by
  rw [← sixSphereStereographic_source v]
  exact sixSphere_stereographicSource_simplyConnected v

/-- Simple-connectivity of the standard six-sphere is exactly the assertion that all its loops are
nullhomotopic.  Path-connectedness is discharged by the existing sphere theorem. -/
public theorem sixSphere_simplyConnected_iff_loops_nullhomotopic :
    SimplyConnectedSpace SixSphere ↔
      ∀ (x : SixSphere) (γ : Path x x), Path.Homotopic γ (Path.refl x) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  exact and_iff_right sixSphere_pathConnectedSpace

/-- It suffices to nullhomotope every loop in the standard six-sphere. -/
public theorem sixSphere_simplyConnected_of_loops_nullhomotopic
    (h : ∀ (x : SixSphere) (γ : Path x x), Path.Homotopic γ (Path.refl x)) :
    SimplyConnectedSpace SixSphere :=
  sixSphere_simplyConnected_iff_loops_nullhomotopic.mpr h

end SphereSixComplex
