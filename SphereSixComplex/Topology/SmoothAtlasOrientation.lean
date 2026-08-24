module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Orientations carried by smooth atlases

Mathlib has linear orientations but no orientation structure for manifolds.  This file supplies the
small atlas-level certificate needed by Poincare duality: a real orientation of the model space
that is preserved by every transition map in the chosen atlas.

It also proves the standard fact that a complex atlas has such an orientation.  The proof restricts
complex derivatives to the reals and uses that their real determinant is the squared norm of the
complex determinant.
-/

@[expose] public section

open scoped ContDiff Manifold

noncomputable section

namespace SphereSixComplex

/-- An orientation of a real `d`-dimensional model space preserved by the transition derivatives
of a chosen smooth atlas.

This intentionally quantifies over `atlas`, not `IsManifold.maximalAtlas`: the maximal smooth atlas
also contains orientation-reversing charts.  A real `IsManifold` hypothesis is kept separate by the
consumer, so the derivative appearing here is known to be the derivative of a smooth transition. -/
public structure SmoothAtlasOrientation (d : ℕ) (E M : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] where
  /-- The selected orientation of the model vector space. -/
  orientation : Orientation ℝ E (Fin d)
  /-- The model really has real dimension `d`. -/
  dimension_eq : Module.finrank ℝ E = d
  /-- Every transition derivative in the selected atlas preserves the orientation. -/
  transitionDerivativePreserves :
    ∀ (e e' : OpenPartialHomeomorph M E), e ∈ atlas E M → e' ∈ atlas E M →
      ∀ x ∈ ((modelWithCornersSelf ℝ E).extendCoordChange e e').source,
        ∃ D : E ≃L[ℝ] E,
          (D : E →L[ℝ] E) = fderivWithin ℝ
              ((modelWithCornersSelf ℝ E).extendCoordChange e e')
              ((modelWithCornersSelf ℝ E).extendCoordChange e e').source x ∧
            Orientation.map (Fin d) D.toLinearEquiv orientation = orientation

/-- A complex manifold is a real manifold on the same chart carrier and with the same selected
atlas. -/
public theorem isManifoldRealOfComplex
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] {n : ℕ∞ω}
    (h : IsManifold (modelWithCornersSelf ℂ E) n M) :
    IsManifold (modelWithCornersSelf ℝ E) n M := by
  let _ : IsManifold (modelWithCornersSelf ℂ E) n M := h
  apply isManifold_of_contDiffOn (modelWithCornersSelf ℝ E) n M
  intro e e' he he'
  have hc := (modelWithCornersSelf ℂ E).contDiffOn_extendCoordChange
    (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ E) (n := n) he)
    (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ E) (n := n) he')
  simpa [ModelWithCorners.extendCoordChange, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm] using hc.restrict_scalars ℝ

/-- A complex-linear equivalence preserves every real orientation of its underlying real vector
space. -/
public theorem complexLinearEquiv_preserves_real_orientation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {d : ℕ}
    (o : Orientation ℝ E (Fin d)) (hd : Module.finrank ℝ E = d)
    (f : E ≃L[ℂ] E) :
    Orientation.map (Fin d) (f.restrictScalars ℝ).toLinearEquiv o = o := by
  apply (Orientation.map_eq_iff_det_pos o
    (f.restrictScalars ℝ).toLinearEquiv (by simpa using hd.symm)).2
  change 0 < LinearMap.det ((f.toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ)
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  exact Complex.normSq_pos.mpr f.toLinearEquiv.isUnit_det'.ne_zero

/-- An atlas orientation of a complex manifold, viewed in its real dimension. -/
public noncomputable def smoothAtlasOrientationOfComplex
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
    (h : IsManifold (modelWithCornersSelf ℂ E) 1 M) :
    SmoothAtlasOrientation (Module.finrank ℝ E) E M := by
  letI : IsManifold (modelWithCornersSelf ℂ E) 1 M := h
  refine ⟨(Module.finBasis ℝ E).orientation, rfl, ?_⟩
  intro e e' he he' x hx
  have hInv := (modelWithCornersSelf ℂ E).isInvertible_fderivWithin_extendCoordChange
    (n := 1) one_ne_zero
    (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ E) (n := 1) he)
    (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ E) (n := 1) he') hx
  obtain ⟨D, hD⟩ := hInv
  refine ⟨D.restrictScalars ℝ, ?_,
    complexLinearEquiv_preserves_real_orientation (Module.finBasis ℝ E).orientation rfl D⟩
  have hdiff : DifferentiableWithinAt ℂ
      ((modelWithCornersSelf ℂ E).extendCoordChange e e')
      ((modelWithCornersSelf ℂ E).extendCoordChange e e').source x :=
    ((modelWithCornersSelf ℂ E).contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ E) (n := 1) he)
      (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ E) (n := 1) he')
      x hx).differentiableWithinAt one_ne_zero
  have hDr := hdiff.restrictScalars_fderivWithin (𝕜 := ℝ)
    ((modelWithCornersSelf ℝ E).uniqueDiffOn_extendCoordChange_source x hx)
  apply ContinuousLinearMap.ext
  intro y
  change D y = fderivWithin ℝ
    ((modelWithCornersSelf ℝ E).extendCoordChange e e')
    ((modelWithCornersSelf ℝ E).extendCoordChange e e').source x y
  rw [show D y = fderivWithin ℂ
      ((modelWithCornersSelf ℂ E).extendCoordChange e e')
      ((modelWithCornersSelf ℂ E).extendCoordChange e e').source x y by
    exact DFunLike.congr_fun hD y]
  exact DFunLike.congr_fun hDr y

end SphereSixComplex
