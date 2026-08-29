/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCarrierGeometry
public import SphereSixComplex.Geometry.LocalDiffeomorphTransport
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Analytic residuals for the infinite `A₂` toric carrier

This module proves that the common algebraic torus is locally biholomorphic in the explicit
glued atlas.  It also develops the local finiteness statements needed for the closed-polydisc
region in the standard toric model.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

private theorem denseTorusCoordinate_contMDiff (i : Fin 3) :
    letI := denseTorusCharts
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞ (fun x : DenseTorus ↦ (x i : ℂ)) := by
  let _ := denseTorusCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
    denseTorusComplexCoordinates_isOpenEmbedding.isManifold_singleton
  have hcoordinates : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ denseTorusComplexCoordinates :=
    contMDiff_isOpenEmbedding denseTorusComplexCoordinates_isOpenEmbedding
  convert (EuclideanSpace.proj (𝕜 := ℂ) i).contMDiff.comp hcoordinates using 1
  rfl

public theorem baseTorusHomeomorph_contMDiff :
    letI := denseTorusCharts
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ baseTorusHomeomorph := by
  let _ := denseTorusCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
    denseTorusComplexCoordinates_isOpenEmbedding.isManifold_singleton
  apply ContMDiff.of_comp_isOpenEmbedding denseTorusComplexCoordinates_isOpenEmbedding
  have hraw : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ RawCoordinates) ∞
      (denseRawCoordinates ∘ baseTorusHomeomorph) := by
    rw [contMDiff_pi_space]
    intro i
    fin_cases i
    · have h := (((denseTorusCoordinate_contMDiff 0).mul
          (denseTorusCoordinate_contMDiff 1)).inv₀
          (fun x ↦ mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))).mul
          (denseTorusCoordinate_contMDiff 2)
      convert h using 1
      funext x
      simp [denseRawCoordinates, baseTorusHomeomorph, baseTorusEquiv]
    · simpa [denseRawCoordinates, baseTorusHomeomorph, baseTorusEquiv] using
        denseTorusCoordinate_contMDiff 0
    · simpa [denseRawCoordinates, baseTorusHomeomorph, baseTorusEquiv] using
        denseTorusCoordinate_contMDiff 1
  have hlinear : ContMDiff (modelWithCornersSelf ℂ RawCoordinates)
      (modelWithCornersSelf ℂ ComplexModel) ∞ rawToComplexModel :=
    contMDiff_iff_contDiff.mpr rawToComplexModel.contDiff
  change ContMDiff (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (rawToComplexModel ∘ denseRawCoordinates ∘ baseTorusHomeomorph)
  simpa only [Function.comp_assoc] using hlinear.comp hraw

public theorem baseTorusHomeomorph_symm_contMDiff :
    letI := denseTorusCharts
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ baseTorusHomeomorph.symm := by
  let _ := denseTorusCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
    denseTorusComplexCoordinates_isOpenEmbedding.isManifold_singleton
  apply ContMDiff.of_comp_isOpenEmbedding denseTorusComplexCoordinates_isOpenEmbedding
  have hraw : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ RawCoordinates) ∞
      (denseRawCoordinates ∘ baseTorusHomeomorph.symm) := by
    rw [contMDiff_pi_space]
    intro i
    fin_cases i
    · simpa [denseRawCoordinates, baseTorusHomeomorph, baseTorusEquiv] using
        denseTorusCoordinate_contMDiff 1
    · simpa [denseRawCoordinates, baseTorusHomeomorph, baseTorusEquiv] using
        denseTorusCoordinate_contMDiff 2
    · have h := ((denseTorusCoordinate_contMDiff 0).mul
          (denseTorusCoordinate_contMDiff 1)).mul (denseTorusCoordinate_contMDiff 2)
      convert h using 1
      funext x
      simp [denseRawCoordinates, baseTorusHomeomorph, baseTorusEquiv]
  have hlinear : ContMDiff (modelWithCornersSelf ℂ RawCoordinates)
      (modelWithCornersSelf ℂ ComplexModel) ∞ rawToComplexModel :=
    contMDiff_iff_contDiff.mpr rawToComplexModel.contDiff
  change ContMDiff (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (rawToComplexModel ∘ denseRawCoordinates ∘ baseTorusHomeomorph.symm)
  simpa only [Function.comp_assoc] using hlinear.comp hraw

/-- The base-chart Laurent coordinate change is a biholomorphism of the canonical dense torus. -/
public noncomputable def baseTorusDiffeomorph :
    letI := denseTorusCharts
    DenseTorus ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ DenseTorus := by
  let _ := denseTorusCharts
  exact
    { toEquiv := baseTorusEquiv
      contMDiff_toFun := baseTorusHomeomorph_contMDiff
      contMDiff_invFun := baseTorusHomeomorph_symm_contMDiff }

/-- The canonical torus-coordinate open embedding, bundled as a partial diffeomorphism. -/
public noncomputable def denseTorusCoordinatePartialDiffeomorph :
    letI := denseTorusCharts
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) DenseTorus ComplexModel ∞ := by
  let _ := denseTorusCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
    denseTorusComplexCoordinates_isOpenEmbedding.isManifold_singleton
  let e := denseTorusComplexCoordinates_isOpenEmbedding.toOpenPartialHomeomorph
    denseTorusComplexCoordinates
  exact
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun :=
        (contMDiff_isOpenEmbedding denseTorusComplexCoordinates_isOpenEmbedding).contMDiffOn
      contMDiffOn_invFun := by
        rw [denseTorusComplexCoordinates_isOpenEmbedding.toOpenPartialHomeomorph_target]
        exact contMDiffOn_isOpenEmbedding_symm
          denseTorusComplexCoordinates_isOpenEmbedding }

private theorem denseTorusComplexCoordinates_baseTorus (x : DenseTorus) :
    denseTorusComplexCoordinates (baseTorusHomeomorph x) =
      rawToComplexModel (baseChartCoordinates x) := by
  rfl

private theorem toricChart_invFun_denseTorusCoordinates (x : DenseTorus) :
    letI := chartedSpace
    (toricChart baseChart).invFun
      (denseTorusComplexCoordinates (baseTorusHomeomorph x)) = carrierTorusEmbedding x := by
  let _ := chartedSpace
  rw [denseTorusComplexCoordinates_baseTorus]
  rw [show rawToComplexModel (baseChartCoordinates x) =
      toricChart baseChart (carrierTorusEmbedding x) by
    rw [carrierTorusEmbedding, toricChart_inclusion]]
  exact (toricChart baseChart).left_inv (carrierTorusEmbedding_mem_toricChart baseChart x)

/-- The explicit dense-torus inclusion is locally biholomorphic for the canonical torus atlas. -/
public theorem carrierTorusEmbedding_isLocalDiffeomorph :
    letI := denseTorusCharts
    letI := chartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ carrierTorusEmbedding := by
  let _ := denseTorusCharts
  let _ := chartedSpace
  intro x
  have hbase := baseTorusDiffeomorph.isLocalDiffeomorph x
  have hcoordinates := denseTorusCoordinatePartialDiffeomorph.isLocalDiffeomorphAt
    (modelWithCornersSelf ℂ ComplexModel) (modelWithCornersSelf ℂ ComplexModel) ∞
    (show baseTorusDiffeomorph x ∈ denseTorusCoordinatePartialDiffeomorph.source by
      simp [denseTorusCoordinatePartialDiffeomorph])
  have hfirst := IsLocalDiffeomorphAt.comp (modelWithCornersSelf ℂ ComplexModel)
    ComplexModel hbase hcoordinates
  have hchart := (toricChart baseChart).symm.isLocalDiffeomorphAt
    (modelWithCornersSelf ℂ ComplexModel) (modelWithCornersSelf ℂ ComplexModel) ∞
    (show denseTorusComplexCoordinates (baseTorusDiffeomorph x) ∈
        (toricChart baseChart).symm.source by simp [toricChart_target])
  have hlocal := IsLocalDiffeomorphAt.comp (modelWithCornersSelf ℂ ComplexModel)
    Carrier hfirst hchart
  have heq : ((toricChart baseChart).symm ∘
      denseTorusCoordinatePartialDiffeomorph ∘ baseTorusDiffeomorph) =
      carrierTorusEmbedding := by
    funext y
    simp only [Function.comp_apply]
    rw [show baseTorusDiffeomorph y = baseTorusHomeomorph y by rfl]
    simpa [denseTorusCoordinatePartialDiffeomorph] using
      toricChart_invFun_denseTorusCoordinates y
  rwa [heq] at hlocal

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
