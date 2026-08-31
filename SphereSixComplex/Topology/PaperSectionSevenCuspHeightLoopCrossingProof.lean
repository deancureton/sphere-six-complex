module

public import SphereSixComplex.Topology.PaperSectionSevenCuspAdaptiveCoverInvariantBasisProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspSwappedCoverGeometryProof

/-!
# Threshold crossings of the actual cusp height loop

The pulled-back affine cover is governed by the reciprocal modular height along the mapping
torus circle.  This file records its continuity and the forced outward threshold crossings.
These facts do not assert uniqueness of the crossings.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContinuousMap

open SphereSixComplex
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The affine height along a fixed fibre point of the actual cusp mapping torus. -/
public noncomputable def actualCuspCylinderHeightLoop
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) : C(unitInterval, ℝ) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let cylinder : C(unitInterval, CircleMappingTorus G.clutching) :=
    (circleMappingTorusCylinderProjection G.clutching).comp
      ⟨fun t ↦ (t, y), continuous_id.prodMk continuous_const⟩
  let collar : C(unitInterval, A.openEmbeddingStarData.collarSource 0) :=
    G.totalHomotopyEquiv.invFun.comp cylinder
  let central : C(unitInterval, A.sectionSevenEllipticCentralImage) :=
    ⟨fun t ↦
      ⟨R.twoDiscCover.cuspToEllipticInteriorMap (collar t),
        R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage _⟩,
      (R.twoDiscCover.cuspToEllipticInteriorMap.hom.continuous.comp
        collar.continuous).subtype_mk _⟩
  exact ⟨fun t ↦ A.sectionSevenEllipticCentralHeight (central t),
    A.sectionSevenEllipticCentralHeight_continuous.comp central.continuous⟩

public theorem actualCuspCylinderHeightLoop_apply
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) (t : unitInterval) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspCylinderHeightLoop R y t =
      A.sectionSevenEllipticCentralHeight
        ⟨R.twoDiscCover.cuspToEllipticInteriorMap
            (G.totalHomotopyEquiv.invFun
              (circleMappingTorusCylinderProjection G.clutching (t, y))),
          R.twoDiscCover.cuspToEllipticInteriorMap_mem_centralImage _⟩ := by
  rfl

/-- The height starts above the upper affine threshold. -/
public theorem two_thirds_lt_actualCuspCylinderHeightLoop_zero
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    (2 / 3 : ℝ) < actualCuspCylinderHeightLoop R y 0 := by
  rw [actualCuspCylinderHeightLoop_apply]
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let p : unitInterval × G.Fiber := (0, y)
  let z := circleMappingTorusCylinderProjection G.clutching p
  rw [R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus z]
  exact two_thirds_lt_actualCuspCylinderReciprocalProduct_re (0, y) (by simp) (by simp)

/-- At phase `5/16`, the actual height is negative. -/
public theorem actualCuspCylinderHeightLoop_five_sixteenths_neg
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    actualCuspCylinderHeightLoop R y
        ⟨5 / 16, by constructor <;> norm_num⟩ < 0 := by
  rw [actualCuspCylinderHeightLoop_apply]
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let t : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
  let p : unitInterval × G.Fiber := (t, y)
  let z := circleMappingTorusCylinderProjection G.clutching p
  rw [R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus z]
  exact actualCuspCylinderReciprocalProduct_re_neg_of_broadLeftSector p
    (by simpa [p, t] using cos_two_pi_mul_five_sixteenths_neg)
    (by simpa [p, t] using sin_two_pi_mul_five_sixteenths_le)

/-- The height returns above the upper affine threshold after one full turn. -/
public theorem two_thirds_lt_actualCuspCylinderHeightLoop_one
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    (2 / 3 : ℝ) < actualCuspCylinderHeightLoop R y 1 := by
  rw [actualCuspCylinderHeightLoop_apply]
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let z := circleMappingTorusCylinderProjection G.clutching (1, y)
  rw [R.twoDiscCover.sectionSevenEllipticCentralHeight_cuspToEllipticInteriorMap_mappingTorus z]
  apply two_thirds_lt_actualCuspCylinderReciprocalProduct_re (1, y)
  · change 0 < Real.cos (2 * Real.pi * 1)
    simp [Real.cos_two_pi]
  · change 50 * |Real.sin (2 * Real.pi * 1)| ≤
      49 * Real.cos (2 * Real.pi * 1)
    simp [Real.cos_two_pi, Real.sin_two_pi]

/-- Every level between `0` and `2/3` is crossed once on each side of the certified negative
phase.  No uniqueness is claimed: the present analytic hypotheses do not exclude additional
crossings. -/
public theorem actualCuspCylinderHeightLoop_crosses_level_on_both_sides
    (R : A.SectionSevenAffineRadialCompletionInput)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber)
    (c : ℝ) (hc0 : 0 ≤ c) (hc2 : c ≤ 2 / 3) :
    let m : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
    ∃ t₀ ∈ Icc (0 : unitInterval) m, actualCuspCylinderHeightLoop R y t₀ = c ∧
      ∃ t₁ ∈ Icc m (1 : unitInterval), actualCuspCylinderHeightLoop R y t₁ = c := by
  let m : unitInterval := ⟨5 / 16, by constructor <;> norm_num⟩
  let h := actualCuspCylinderHeightLoop R y
  have hzero : (2 / 3 : ℝ) < h 0 :=
    two_thirds_lt_actualCuspCylinderHeightLoop_zero R y
  have hm : h m < 0 := by
    simpa [h, m] using actualCuspCylinderHeightLoop_five_sixteenths_neg R y
  have hone : (2 / 3 : ℝ) < h 1 :=
    two_thirds_lt_actualCuspCylinderHeightLoop_one R y
  have hleftMem : c ∈ Icc (h m) (h 0) := by
    constructor <;> linarith
  have hrightMem : c ∈ Icc (h m) (h 1) := by
    constructor <;> linarith
  have hm_le : (0 : unitInterval) ≤ m := by norm_num [m]
  have hm_one : m ≤ (1 : unitInterval) := by
    change (5 / 16 : ℝ) ≤ 1
    norm_num
  obtain ⟨t₀, ht₀, hvalue₀⟩ :=
    intermediate_value_Icc' hm_le h.continuous.continuousOn hleftMem
  obtain ⟨t₁, ht₁, hvalue₁⟩ :=
    intermediate_value_Icc hm_one h.continuous.continuousOn hrightMem
  exact ⟨t₀, ht₀, hvalue₀, t₁, ht₁, hvalue₁⟩

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
