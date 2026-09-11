module

public import SphereSixComplex.Prerequisites.Periods.Uniformization.ExactSourceAssembly
import all SphereSixComplex.Prerequisites.Periods.Uniformization.ExactSourceAssembly
public import SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarTriangleReflection
import all SphereSixComplex.Prerequisites.Periods.Uniformization.ScalarTriangleReflection
public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianTriangleGeometry
import all SphereSixComplex.Prerequisites.TriangleGroup.FuchsianTriangleGeometry
public import Mathlib.Analysis.Complex.OpenMapping
import all Mathlib.Analysis.Complex.OpenMapping

@[expose] public section

/-!
# Formal assembly of a globally reflected scalar coordinate

The analytic continuation step naturally produces a scalar function on the complex upper
half-plane together with the three Schwarz-reflection identities.  This file discharges two
global obligations formally:

* the three reflection identities imply invariance under every element of `C₃ * C₄`;
* holomorphicity and the distinct normalized values `0` and `1` imply openness by the complex
  open-mapping theorem.

Thus the final Schwarz construction need not carry either group invariance or openness as an
extra field.
-/

open Complex Set Topology UpperHalfPlane
open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods.TriangleReflections
open SphereSixComplex.Periods.ExactSourceAssembly
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover










/-- The scalar upper half-plane, as a subset of `ℂ`. -/
def scalarUpperHalfPlane : Set ℂ := {z | 0 < z.im}

theorem scalarUpperHalfPlane_isOpen : IsOpen scalarUpperHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_im

theorem scalarUpperHalfPlane_isPreconnected : IsPreconnected scalarUpperHalfPlane := by
  exact (convex_halfSpace_im_gt 0).isPreconnected

/-- A holomorphic scalar function with two distinct values restricts to an open map on the upper
half-plane. -/
theorem isOpenMap_upperHalfPlane_of_differentiableOn_of_ne
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F scalarUpperHalfPlane)
    (z w : UpperHalfPlane) (hzw : F z ≠ F w) :
    IsOpenMap (fun u : UpperHalfPlane ↦ F (u : ℂ)) := by
  have hAnalytic : AnalyticOnNhd ℂ F scalarUpperHalfPlane :=
    hF.analyticOnNhd scalarUpperHalfPlane_isOpen
  rcases hAnalytic.is_constant_or_isOpen scalarUpperHalfPlane_isPreconnected with
      hconstant | hopen
  · obtain ⟨c, hc⟩ := hconstant
    exact (hzw ((hc z z.im_pos).trans (hc w w.im_pos).symm)).elim
  · intro s hs
    have hcoeOpen : IsOpen (((↑) : UpperHalfPlane → ℂ) '' s) :=
      UpperHalfPlane.isOpenEmbedding_coe.isOpenMap s hs
    have hcoeSub : ((↑) : UpperHalfPlane → ℂ) '' s ⊆ scalarUpperHalfPlane := by
      rintro _ ⟨u, -, rfl⟩
      exact u.im_pos
    have himageOpen := hopen _ hcoeSub hcoeOpen
    convert himageOpen using 1
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u : ℂ), ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩


end SphereSixComplex.Periods.SourceChamberTopology
